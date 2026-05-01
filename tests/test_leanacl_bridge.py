from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "leanacl_bridge.py"
FIXTURES = REPO_ROOT / "fixtures" / "leanacl_bridge"
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from leanacl_bridge import BridgeError, normalize_prediction  # noqa: E402


class NormalizationTests(unittest.TestCase):
    def test_aliases_are_normalized(self) -> None:
        with (FIXTURES / "alias_prediction.json").open(encoding="utf-8") as handle:
            prediction = json.load(handle)

        normalized = normalize_prediction(prediction)

        self.assertTrue(normalized["llm_allowed"])
        self.assertEqual(normalized["requested_permission"], "edit")
        self.assertEqual(normalized["resource"]["ownerOrg"], 1)
        self.assertEqual(normalized["resource"]["resourcetype"], "storage")
        self.assertEqual(normalized["user"]["memberships"][0]["orgId"], 1)
        self.assertEqual(normalized["user"]["memberships"][0]["role"], "devops")

    def test_expected_allowed_alias_is_normalized(self) -> None:
        prediction = {
            "expected_allowed": False,
            "user": {"id": 1, "memberships": [{"orgId": 1, "role": "manager"}]},
            "resource": {"ownerOrg": 1, "resourcetype": "data", "sensitivity": False},
            "requested_permission": "read",
        }

        normalized = normalize_prediction(prediction)

        self.assertFalse(normalized["llm_allowed"])

    def test_unknown_role_is_rejected_before_lean(self) -> None:
        prediction = {
            "llm_allowed": True,
            "user": {"id": 1, "memberships": [{"orgId": 1, "role": "admin"}]},
            "resource": {"ownerOrg": 1, "resourcetype": "data", "sensitivity": False},
            "requested_permission": "read",
        }

        with self.assertRaisesRegex(BridgeError, "unknown value"):
            normalize_prediction(prediction)

    def test_unknown_permission_is_rejected_before_lean(self) -> None:
        prediction = {
            "llm_allowed": True,
            "user": {"id": 1, "memberships": [{"orgId": 1, "role": "manager"}]},
            "resource": {"ownerOrg": 1, "resourcetype": "data", "sensitivity": False},
            "requested_permission": "administer",
        }

        with self.assertRaisesRegex(BridgeError, "unknown value"):
            normalize_prediction(prediction)

    def test_unknown_resource_type_is_rejected_before_lean(self) -> None:
        prediction = {
            "llm_allowed": True,
            "user": {"id": 1, "memberships": [{"orgId": 1, "role": "manager"}]},
            "resource": {"ownerOrg": 1, "resourcetype": "network", "sensitivity": False},
            "requested_permission": "read",
        }

        with self.assertRaisesRegex(BridgeError, "unknown value"):
            normalize_prediction(prediction)

    def test_malformed_prediction_is_rejected_before_lean(self) -> None:
        prediction = {
            "llm_allowed": "yes",
            "user": {"id": True, "memberships": []},
            "resource": {"ownerOrg": 1, "resourcetype": "data", "sensitivity": False},
            "requested_permission": "read",
        }

        with self.assertRaisesRegex(BridgeError, "boolean"):
            normalize_prediction(prediction)


class LeanPredictionTests(unittest.TestCase):
    def run_verify(self, fixture_name: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "verify", str(FIXTURES / fixture_name)],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_correct_allowed_prediction_passes(self) -> None:
        completed = self.run_verify("allowed_sensitive_manager.json")

        self.assertEqual(completed.returncode, 0, msg=completed.stderr)
        verdict = json.loads(completed.stdout)
        self.assertTrue(verdict["llm_allowed"])
        self.assertTrue(verdict["lean_allowed"])
        self.assertTrue(verdict["prediction_correct"])
        self.assertEqual(verdict["grant"], "delete")

    def test_correct_denied_prediction_passes(self) -> None:
        completed = self.run_verify("denied_sensitive_developer.json")

        self.assertEqual(completed.returncode, 0, msg=completed.stderr)
        verdict = json.loads(completed.stdout)
        self.assertFalse(verdict["llm_allowed"])
        self.assertFalse(verdict["lean_allowed"])
        self.assertTrue(verdict["prediction_correct"])
        self.assertEqual(verdict["reason"], "denied_sensitive_data_requires_manager")

    def test_wrong_prediction_fails(self) -> None:
        completed = self.run_verify("wrong_sensitive_developer.json")

        self.assertEqual(completed.returncode, 1, msg=completed.stderr)
        verdict = json.loads(completed.stdout)
        self.assertTrue(verdict["llm_allowed"])
        self.assertFalse(verdict["lean_allowed"])
        self.assertFalse(verdict["prediction_correct"])


class RunPromptsTests(unittest.TestCase):
    def test_run_prompts_reports_prediction_agreement(self) -> None:
        fixture = FIXTURES / "allowed_sensitive_manager.json"
        prompts = {
            "prompts": [
                {"id": "a", "prompt": "ignored for this stub"},
                "second prompt",
            ]
        }
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".json",
            delete=False,
        ) as handle:
            json.dump(prompts, handle)
            prompts_path = Path(handle.name)

        try:
            env = os.environ.copy()
            env["LEANACL_BRIDGE_LLM_STUB_JSON"] = str(fixture)
            completed = subprocess.run(
                [sys.executable, str(SCRIPT), "run_prompts", str(prompts_path)],
                cwd=REPO_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            prompts_path.unlink(missing_ok=True)

        self.assertEqual(completed.returncode, 0, msg=completed.stderr)
        lines = [line for line in completed.stdout.splitlines() if line.strip()]
        self.assertEqual(len(lines), 2)
        for index, line in enumerate(lines):
            record = json.loads(line)
            self.assertEqual(record["index"], index)
            self.assertTrue(record["llm_allowed"])
            self.assertTrue(record["lean_allowed"])
            self.assertTrue(record["llm_verified_by_lean"])
            self.assertTrue(record["verdict"]["prediction_correct"])

    def test_run_prompts_exits_nonzero_for_wrong_prediction(self) -> None:
        fixture = FIXTURES / "wrong_sensitive_developer.json"
        prompts = {"prompts": ["ignored for this stub"]}
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".json",
            delete=False,
        ) as handle:
            json.dump(prompts, handle)
            prompts_path = Path(handle.name)

        try:
            env = os.environ.copy()
            env["LEANACL_BRIDGE_LLM_STUB_JSON"] = str(fixture)
            completed = subprocess.run(
                [sys.executable, str(SCRIPT), "run_prompts", str(prompts_path)],
                cwd=REPO_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            prompts_path.unlink(missing_ok=True)

        self.assertEqual(completed.returncode, 1)
        record = json.loads(completed.stdout)
        self.assertFalse(record["llm_verified_by_lean"])
        self.assertFalse(record["verdict"]["prediction_correct"])

    def test_run_prompts_requires_openai_or_stub(self) -> None:
        prompts = {"prompts": ["only a prompt"]}
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".json",
            delete=False,
        ) as handle:
            json.dump(prompts, handle)
            prompts_path = Path(handle.name)

        try:
            env = os.environ.copy()
            env.pop("OPENAI_API_KEY", None)
            env.pop("LEANACL_BRIDGE_LLM_STUB_JSON", None)
            completed = subprocess.run(
                [sys.executable, str(SCRIPT), "run_prompts", str(prompts_path)],
                cwd=REPO_ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            prompts_path.unlink(missing_ok=True)

        self.assertEqual(completed.returncode, 2)
        self.assertIn("OPENAI_API_KEY is not set", completed.stderr)


if __name__ == "__main__":
    unittest.main()
