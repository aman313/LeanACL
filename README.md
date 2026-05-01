# LeanACL

This repository does two related things:

1. **LeanACL (the Lean library)** — a formal model of an organization-scoped access-control policy: users with per-org roles, resources (`storage` / `compute` / `data`), optional sensitivity on `data`, and permissions `read` ≤ `edit` ≤ `delete`. The executable policy is `grant`; permitted access is `Can`. Theorems in `LeanACL/Theorems.lean` state security properties (e.g. sensitive-data lockdown, cross-org edit denial).

2. **LLM evaluation harness (Python + `leanacl_verify`)** — a small workflow to test whether a **large language model** can **predict allow/deny** for a scenario **consistently with Lean**. The LLM must output structured JSON that includes both its **prediction** (`llm_allowed`) and the **scenario facts** (`user`, `resource`, `requested_permission`). **Lean does not trust the LLM**: it recomputes access from those facts and checks whether `llm_allowed` matches the formal decision.

If you only care about the proofs and policy, use the Lean library and `lake build LeanACL`. If you care about **model vs. spec alignment**, use the bridge and fixtures below.

---

## Problem setup (LLM ↔ Lean)

**Goal:** Treat LeanACL as ground truth and measure whether an LLM’s allow/deny prediction matches it.

**Inputs to the model (conceptually):**

- A **natural-language scenario** (orgs, user memberships, resource type/owner/sensitivity, requested permission). In batch mode this lives in a **user message** built from your prompts JSON file (see `fixtures/leanacl_bridge/input_prompts.json`).
- A **fixed policy summary** in the **system message** (same for every call from `scripts/leanacl_bridge.py`). The model must follow this summary when deciding `llm_allowed`.

**Output from the model (machine-readable):**

- One JSON object per scenario, constrained by OpenAI **structured outputs** (`response_format.type = json_schema`, strict schema). Required fields include `llm_allowed`, `user`, `resource`, `requested_permission`, plus metadata strings `trace_id`, `prompt_version`, `llm_model`. See [LeanACL/bridge_schema.md](LeanACL/bridge_schema.md).

**What Lean does:**

- The verifier (`lake exe leanacl_verify`) reads that JSON, decodes `User` / `Resource` / `Permission`, computes whether `Can user resource requested_permission` holds → `lean_allowed`, and sets `prediction_correct := (llm_allowed == lean_allowed)` in the verdict.

So: **the LLM predicts**; **Lean adjudicates**; the bridge **compares**.

---

## LLM request shape (OpenAI Chat Completions)

For each prompt, `scripts/leanacl_bridge.py` sends an HTTP `POST` to `{OPENAI_BASE_URL}/chat/completions` with a body like:

```json
{
  "model": "<from OPENAI_MODEL or --model, default gpt-4o-mini>",
  "response_format": {
    "type": "json_schema",
    "json_schema": { "name": "leanacl_prediction", "strict": true, "schema": { "...": "see leanacl_bridge.py leanacl_prediction_json_schema()" } }
  },
  "messages": [
    { "role": "system", "content": "<see below>" },
    { "role": "user", "content": "<one prompt string from your prompts file>" }
  ]
}
```

The **user** `content` is exactly the string from each entry in your prompts file (for example the `"prompt"` field in `fixtures/leanacl_bridge/input_prompts.json`). Those strings should describe the scenario and ask the model to decide allow/deny and fill the structured fields (including `trace_id` / `prompt_version` / `llm_model` as instructed in the prompt).

### System message (fixed in code)

This is the full `role: system` text sent by the bridge (policy summary the model should use when setting `llm_allowed`):

```
You are evaluating LeanACL access-control scenarios. Return one structured prediction object. Include the scenario facts and set llm_allowed to your allow/deny decision.

Policy summary: same-org users can read non-sensitive resources. Same-org managers can edit/delete data. Same-org devops can edit/delete non-data resources. Permission delete implies edit and read; edit implies read. Cross-org managers can read non-sensitive resources. Cross-org developers can read non-sensitive data. Cross-org devops can read non-data resources. Sensitive data is deny-override: only same-org managers have access, and they get delete/edit/read.
```

*(Source of truth: `openai_prediction_json()` in `scripts/leanacl_bridge.py`.)*

### User message (your prompts file)

Examples live in `fixtures/leanacl_bridge/input_prompts.json`. Each item is either a string or an object with `"prompt": "..."`. That string is the **entire** user message for that API call — it should spell out org IDs, user id and memberships, resource facts, requested permission, and any metadata you want echoed back (`trace_id`, `prompt_version`, `llm_model`).

### Model reply (structured JSON)

The API returns assistant `content` that parses to one object matching the strict schema, for example:

```json
{
  "trace_id": "prompt-sensitive-manager-delete",
  "prompt_version": "input-prompts-v1",
  "llm_model": "gpt-4o-mini",
  "llm_allowed": true,
  "user": { "id": 101, "memberships": [{ "orgId": 1, "role": "manager" }] },
  "resource": { "ownerOrg": 1, "resourcetype": "data", "sensitivity": true },
  "requested_permission": "delete"
}
```

The bridge then **normalizes** minor aliases (e.g. `write` → `edit`, `dev_ops` → `devops`) before calling Lean.

---

## End-to-end flow (`run_prompts`)

1. Read prompts file → one user message per prompt.
2. POST to OpenAI with system message + structured JSON schema.
3. Parse response → normalize → write temp JSON → `lake exe leanacl_verify …`.
4. Print one JSON line per prompt with `llm_allowed`, `lean_allowed`, `llm_verified_by_lean`, and full `verdict`.

---

## Prerequisites

- [Lake](https://github.com/leanprover/lean4) and Lean **4.29.0** (see `lean-toolchain`; [elan](https://github.com/leanprover/elan) is typical).
- **Python 3** (stdlib only; no pip packages required for the bridge).

## First-time setup

From this directory:

```bash
cd /path/to/LeanACL
lake update    # fetches Mathlib and writes lake-manifest.json
lake build LeanACL
lake build leanacl_verify
```

## Build targets

| Command | What it does |
|---------|----------------|
| `lake build LeanACL` | Builds the `LeanACL` library (terms, policy, theorems, examples). |
| `lake build leanacl_verify` | Builds the JSON verifier executable. |

## Python bridge

The script calls OpenAI (HTTPS, stdlib `urllib`) unless you use the offline stub.

### Environment variables

| Variable | Required? | Purpose |
|----------|------------|---------|
| `OPENAI_API_KEY` | Yes for live LLM | Bearer token for OpenAI Chat Completions. |
| `OPENAI_BASE_URL` | No | API base URL; default `https://api.openai.com/v1`. |
| `OPENAI_MODEL` or `LEANACL_OPENAI_MODEL` | No | Model name; default `gpt-4o-mini`. |
| `LEANACL_BRIDGE_LLM_STUB_JSON` | No | Path to a fixed prediction JSON file; when set, skips the network and returns that file for every prompt (tests / CI). |

### Verify one prediction JSON file

The file must include `llm_allowed` (the LLM’s prediction) plus `user`, `resource`, and `requested_permission`. See `LeanACL/bridge_schema.md` and `fixtures/leanacl_bridge/*.json`.

```bash
python3 scripts/leanacl_bridge.py verify fixtures/leanacl_bridge/allowed_sensitive_manager.json
```

- Prints a JSON verdict to stdout (`llm_allowed`, `lean_allowed`, `prediction_correct`, `reason`, `grant`, …).
- Exit code **0** if the LLM prediction matches Lean, **1** if they disagree.

### Run many prompts (batch)

Prompts file: `fixtures/leanacl_bridge/input_prompts.json` (or your own), shaped as `{ "prompts": [ ... ] }` or a JSON array of prompt strings/objects with a `prompt` field.

```bash
export OPENAI_API_KEY="sk-..."
python3 scripts/leanacl_bridge.py run_prompts fixtures/leanacl_bridge/input_prompts.json
```

Optional model override:

```bash
python3 scripts/leanacl_bridge.py run_prompts fixtures/leanacl_bridge/input_prompts.json --model gpt-4o-mini
```

Each line of stdout is one JSON object per prompt, including `llm_verified_by_lean` (true when `llm_allowed` matches Lean). The process exits **non-zero** if any prompt fails the pipeline or the prediction is wrong.

### Offline / CI example

```bash
export LEANACL_BRIDGE_LLM_STUB_JSON="$(pwd)/fixtures/leanacl_bridge/allowed_sensitive_manager.json"
python3 scripts/leanacl_bridge.py run_prompts fixtures/leanacl_bridge/input_prompts.json
```

## Unit tests

```bash
python3 -m unittest tests/test_leanacl_bridge.py
```

## Lean verifier only (no Python)

```bash
lake exe leanacl_verify fixtures/leanacl_bridge/allowed_sensitive_manager.json
# or write verdict to a file:
lake exe leanacl_verify fixtures/leanacl_bridge/allowed_sensitive_manager.json /tmp/verdict.json
```

## Schema and policy notes

- Full JSON contract: [LeanACL/bridge_schema.md](LeanACL/bridge_schema.md).
- Library entrypoint imports: [LeanACL.lean](LeanACL.lean).
