#!/usr/bin/env python3
"""Run LLM ACL predictions through LeanACL verification.

The LLM predicts whether a requested access should be allowed and emits the
scenario facts it used. LeanACL independently computes the authoritative answer;
the bridge reports whether the LLM prediction matches Lean.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Mapping


ROLE_ALIASES = {
    "manager": "manager",
    "developer": "developer",
    "devops": "devops",
    "dev_ops": "devops",
    "dev-ops": "devops",
    "ops": "devops",
}

RESOURCE_TYPE_ALIASES = {
    "storage": "storage",
    "compute": "compute",
    "data": "data",
}

PERMISSION_ALIASES = {
    "read": "read",
    "edit": "edit",
    "write": "edit",
    "delete": "delete",
    "remove": "delete",
}


class BridgeError(ValueError):
    """Raised when a prediction cannot be normalized or verified."""


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _expect_object(value: Any, path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BridgeError(f"{path} must be an object")
    return value


def _expect_bool(value: Any, path: str) -> bool:
    if not isinstance(value, bool):
        raise BridgeError(f"{path} must be a boolean")
    return value


def _expect_int(value: Any, path: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise BridgeError(f"{path} must be a non-negative integer")
    return value


def _expect_string(value: Any, path: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise BridgeError(f"{path} must be a non-empty string")
    return value.strip()


def _canonical_enum(value: Any, aliases: dict[str, str], path: str) -> str:
    raw = _expect_string(value, path).lower().replace(" ", "_")
    try:
        return aliases[raw]
    except KeyError as exc:
        allowed = ", ".join(sorted(set(aliases.values())))
        raise BridgeError(f"{path} has unknown value {value!r}; expected one of: {allowed}") from exc


def normalize_prediction(prediction: dict[str, Any]) -> dict[str, Any]:
    payload = _expect_object(prediction, "$")

    user = _expect_object(payload.get("user"), "$.user")
    memberships = payload.get("memberships", user.get("memberships"))
    if not isinstance(memberships, list):
        raise BridgeError("$.user.memberships must be a list")

    normalized_memberships: list[dict[str, Any]] = []
    for index, membership_value in enumerate(memberships):
        membership = _expect_object(membership_value, f"$.user.memberships[{index}]")
        org_value = membership.get("orgId", membership.get("org_id"))
        normalized_memberships.append(
            {
                "orgId": _expect_int(org_value, f"$.user.memberships[{index}].orgId"),
                "role": _canonical_enum(
                    membership.get("role"),
                    ROLE_ALIASES,
                    f"$.user.memberships[{index}].role",
                ),
            }
        )

    resource = _expect_object(payload.get("resource"), "$.resource")
    resource_type = resource.get("resourcetype", resource.get("resource_type"))

    normalized = {
        "trace_id": payload.get("trace_id"),
        "prompt_version": payload.get("prompt_version"),
        "llm_model": payload.get("llm_model"),
        "llm_allowed": _expect_bool(
            payload.get("llm_allowed", payload.get("expected_allowed")),
            "$.llm_allowed",
        ),
        "user": {
            "id": _expect_int(user.get("id"), "$.user.id"),
            "memberships": normalized_memberships,
        },
        "resource": {
            "ownerOrg": _expect_int(
                resource.get("ownerOrg", resource.get("owner_org")),
                "$.resource.ownerOrg",
            ),
            "resourcetype": _canonical_enum(
                resource_type,
                RESOURCE_TYPE_ALIASES,
                "$.resource.resourcetype",
            ),
            "sensitivity": _expect_bool(resource.get("sensitivity"), "$.resource.sensitivity"),
        },
        "requested_permission": _canonical_enum(
            payload.get("requested_permission", payload.get("permission")),
            PERMISSION_ALIASES,
            "$.requested_permission",
        ),
    }

    for optional_key in ("trace_id", "prompt_version", "llm_model"):
        value = normalized[optional_key]
        if value is not None:
            normalized[optional_key] = _expect_string(value, f"$.{optional_key}")

    return normalized

def read_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        value = json.load(handle)
    return _expect_object(value, str(path))


def read_json_value(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _first_json_object(text: str) -> dict[str, Any]:
    text = text.strip()
    if not text:
        raise BridgeError("LLM returned an empty response")

    fence = re.search(r"```(?:json)?\s*([\s\S]*?)\s*```", text, flags=re.IGNORECASE)
    if fence:
        text = fence.group(1).strip()

    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        start = text.find("{")
        end = text.rfind("}")
        if start == -1 or end == -1 or end <= start:
            raise BridgeError("LLM response was not valid JSON") from None
        try:
            value = json.loads(text[start : end + 1])
        except json.JSONDecodeError as exc:
            raise BridgeError(f"LLM response was not valid JSON: {exc}") from exc

    return _expect_object(value, "llm response")


def _openai_base_url() -> str:
    raw = os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1").strip().rstrip("/")
    return raw or "https://api.openai.com/v1"


def _openai_model(cli_model: str | None) -> str:
    if cli_model:
        return cli_model
    return os.environ.get("OPENAI_MODEL", os.environ.get("LEANACL_OPENAI_MODEL", "gpt-4o-mini")).strip()


def leanacl_prediction_json_schema() -> dict[str, Any]:
    return {
        "name": "leanacl_prediction",
        "strict": True,
        "schema": {
            "type": "object",
            "additionalProperties": False,
            "properties": {
                "trace_id": {"type": "string"},
                "prompt_version": {"type": "string"},
                "llm_model": {"type": "string"},
                "llm_allowed": {"type": "boolean"},
                "user": {
                    "type": "object",
                    "additionalProperties": False,
                    "properties": {
                        "id": {"type": "integer", "minimum": 0},
                        "memberships": {
                            "type": "array",
                            "items": {
                                "type": "object",
                                "additionalProperties": False,
                                "properties": {
                                    "orgId": {"type": "integer", "minimum": 0},
                                    "role": {
                                        "type": "string",
                                        "enum": ["manager", "developer", "devops"],
                                    },
                                },
                                "required": ["orgId", "role"],
                            },
                        },
                    },
                    "required": ["id", "memberships"],
                },
                "resource": {
                    "type": "object",
                    "additionalProperties": False,
                    "properties": {
                        "ownerOrg": {"type": "integer", "minimum": 0},
                        "resourcetype": {
                            "type": "string",
                            "enum": ["storage", "compute", "data"],
                        },
                        "sensitivity": {"type": "boolean"},
                    },
                    "required": ["ownerOrg", "resourcetype", "sensitivity"],
                },
                "requested_permission": {
                    "type": "string",
                    "enum": ["read", "edit", "delete"],
                },
            },
            "required": [
                "trace_id",
                "prompt_version",
                "llm_model",
                "llm_allowed",
                "user",
                "resource",
                "requested_permission",
            ],
        },
    }


def openai_prediction_json(prompt: str, model: str | None) -> dict[str, Any]:
    """Call OpenAI and parse one LeanACL prediction object from the reply."""
    stub_path = os.environ.get("LEANACL_BRIDGE_LLM_STUB_JSON")
    if stub_path:
        return read_json(Path(stub_path))

    api_key = os.environ.get("OPENAI_API_KEY", "").strip()
    if not api_key:
        raise BridgeError(
            "OPENAI_API_KEY is not set (or use LEANACL_BRIDGE_LLM_STUB_JSON for offline tests)"
        )

    payload = {
        "model": _openai_model(model),
        "response_format": {
            "type": "json_schema",
            "json_schema": leanacl_prediction_json_schema(),
        },
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are evaluating LeanACL access-control scenarios. "
                    "Return one structured prediction object. Include the scenario facts "
                    "and set llm_allowed to your allow/deny decision.\n\n"
                    "Policy summary: same-org users can read non-sensitive resources. "
                    "Same-org managers can edit/delete data. Same-org devops can "
                    "edit/delete non-data resources. Permission delete implies edit "
                    "and read; edit implies read. Cross-org managers can read "
                    "non-sensitive resources. Cross-org developers can read "
                    "non-sensitive data. Cross-org devops can read non-data resources. "
                    "Sensitive data is deny-override: only same-org managers have "
                    "access, and they get delete/edit/read."
                ),
            },
            {"role": "user", "content": prompt},
        ],
    }
    data = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        f"{_openai_base_url()}/chat/completions",
        data=data,
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )

    try:
        with urllib.request.urlopen(request, timeout=120) as response:
            body = response.read().decode("utf-8")
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise BridgeError(f"OpenAI HTTP {exc.code}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise BridgeError(f"OpenAI request failed: {exc}") from exc

    try:
        envelope = json.loads(body)
    except json.JSONDecodeError as exc:
        raise BridgeError(f"OpenAI returned non-JSON: {exc}") from exc

    try:
        content = envelope["choices"][0]["message"]["content"]
    except (KeyError, IndexError, TypeError) as exc:
        raise BridgeError(f"Unexpected OpenAI response shape: {envelope}") from exc
    if not isinstance(content, str):
        raise BridgeError("OpenAI message content was not a string")

    return _first_json_object(content)


def verify_prediction_path(prediction_path: Path, verdict_output: Path | None) -> dict[str, Any]:
    root = repo_root()
    with tempfile.TemporaryDirectory(prefix="leanacl-bridge-") as temp_dir:
        output_path = verdict_output or Path(temp_dir) / "verdict.json"
        completed = subprocess.run(
            ["lake", "exe", "leanacl_verify", str(prediction_path), str(output_path)],
            cwd=root,
            text=True,
            capture_output=True,
            check=False,
        )
        if completed.returncode != 0:
            raise BridgeError(completed.stderr.strip() or completed.stdout.strip())
        return read_json(output_path)


def verify_normalized_prediction(
    prediction: dict[str, Any],
    verdict_output: Path | None = None,
) -> dict[str, Any]:
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".json",
        delete=False,
    ) as handle:
        json.dump(prediction, handle, indent=2, sort_keys=True)
        handle.write("\n")
        prediction_path = Path(handle.name)

    try:
        return verify_prediction_path(prediction_path, verdict_output)
    finally:
        prediction_path.unlink(missing_ok=True)


def command_verify(args: argparse.Namespace) -> int:
    prediction = normalize_prediction(read_json(args.input))
    if args.normalized_output:
        write_json(args.normalized_output, prediction)
    verdict = verify_normalized_prediction(prediction, args.verdict_output)
    print(json.dumps(verdict, indent=2, sort_keys=True))
    return 0 if verdict.get("prediction_correct") else 1


def _prompt_entry_from_indexed_item(index: int, item: Any) -> tuple[str | None, str]:
    if isinstance(item, str):
        return None, item
    if isinstance(item, dict):
        prompt = item.get("prompt", item.get("text"))
        if not isinstance(prompt, str) or not prompt.strip():
            raise BridgeError(
                f"$.prompts[{index}] must be a string or an object with non-empty "
                f"'prompt' or 'text'"
            )
        prompt_id = item.get("id")
        if prompt_id is not None and not isinstance(prompt_id, (str, int)):
            raise BridgeError(f"$.prompts[{index}].id must be a string or integer when present")
        if isinstance(prompt_id, int):
            prompt_id = str(prompt_id)
        if isinstance(prompt_id, str) and not prompt_id.strip():
            prompt_id = None
        return prompt_id, prompt.strip()
    raise BridgeError(f"$.prompts[{index}] must be a string or an object")


def load_prompts_file(path: Path) -> list[tuple[str | None, str]]:
    root = read_json_value(path)
    if isinstance(root, list):
        prompts_raw = root
    elif isinstance(root, Mapping):
        prompts_raw = root.get("prompts")
        if prompts_raw is None:
            raise BridgeError("$.prompts is required when the prompts file is an object")
    else:
        raise BridgeError("prompts file must be a JSON array or a JSON object")

    if not isinstance(prompts_raw, list):
        raise BridgeError("$.prompts must be a JSON array")

    return [_prompt_entry_from_indexed_item(index, item) for index, item in enumerate(prompts_raw)]


def command_run_prompts(args: argparse.Namespace) -> int:
    prompt_entries = load_prompts_file(args.prompts_file)

    stub_path = os.environ.get("LEANACL_BRIDGE_LLM_STUB_JSON")
    if not stub_path and not os.environ.get("OPENAI_API_KEY", "").strip():
        raise BridgeError(
            "OPENAI_API_KEY is not set (or use LEANACL_BRIDGE_LLM_STUB_JSON for offline tests)"
        )

    failures = 0
    for index, (prompt_id, prompt_text) in enumerate(prompt_entries):
        record: dict[str, Any] = {
            "index": index,
            "id": prompt_id,
            "llm_verified_by_lean": False,
        }
        try:
            prediction = normalize_prediction(openai_prediction_json(prompt_text + "\n", args.model))
            verdict = verify_normalized_prediction(prediction)
            record.update(
                {
                    "trace_id": prediction.get("trace_id"),
                    "llm_allowed": verdict["llm_allowed"],
                    "lean_allowed": verdict["lean_allowed"],
                    "llm_verified_by_lean": verdict["prediction_correct"],
                    "verdict": verdict,
                }
            )
            if not verdict["prediction_correct"]:
                failures += 1
        except (BridgeError, OSError) as exc:
            record["error"] = str(exc)
            failures += 1
        print(json.dumps(record, sort_keys=True))

    return 1 if failures else 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run LLM LeanACL allow/deny predictions through Lean verification"
    )
    subparsers = parser.add_subparsers(required=True)

    verify = subparsers.add_parser("verify", help="Verify one existing LLM prediction JSON file")
    verify.add_argument("input", type=Path)
    verify.add_argument("--normalized-output", type=Path)
    verify.add_argument("--verdict-output", type=Path)
    verify.set_defaults(func=command_verify)

    run_prompts = subparsers.add_parser(
        "run-prompts",
        aliases=["run_prompts"],
        help="Run many prompts through OpenAI and compare each LLM prediction with Lean",
    )
    run_prompts.add_argument("prompts_file", type=Path)
    run_prompts.add_argument(
        "--model",
        help="OpenAI model name (defaults to OPENAI_MODEL / LEANACL_OPENAI_MODEL / gpt-4o-mini)",
    )
    run_prompts.set_defaults(func=command_run_prompts)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except (BridgeError, OSError, json.JSONDecodeError) as exc:
        print(f"leanacl_bridge: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
