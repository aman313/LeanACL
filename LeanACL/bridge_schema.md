# LeanACL Bridge Schema

The LeanACL bridge checks whether an LLM's access-control prediction agrees
with LeanACL. Python asks the LLM for a structured prediction, normalizes basic
aliases, and then Lean computes the authoritative policy result.

## Prediction Payload

The LLM must output one JSON object with:

```json
{
  "trace_id": "optional-correlation-id",
  "prompt_version": "prompt-version",
  "llm_model": "model-name",
  "llm_allowed": true,
  "user": {
    "id": 1,
    "memberships": [
      { "orgId": 1, "role": "manager" }
    ]
  },
  "resource": {
    "ownerOrg": 1,
    "resourcetype": "data",
    "sensitivity": true
  },
  "requested_permission": "read"
}
```

`llm_allowed` is the LLM's allow/deny prediction. Lean independently evaluates
`Can user resource requested_permission` and compares the result with this
field.

## Canonical Enum Values

Roles:

- `manager`
- `developer`
- `devops`

Resource types:

- `storage`
- `compute`
- `data`

Permissions:

- `read`
- `edit`
- `delete`

## Python Normalization

Python accepts a small alias set before writing the normalized artifact:

- role aliases: `dev_ops`, `dev-ops`, `ops` -> `devops`
- resource aliases: `resource_type` -> `resourcetype`; `owner_org` -> `ownerOrg`
- permission aliases: `remove` -> `delete`, `write` -> `edit`
- prediction alias: `expected_allowed` -> `llm_allowed`

After normalization, the JSON passed to Lean contains canonical enum strings
and the exact field names shown above.

## Verdict Payload

The Lean verifier writes:

```json
{
  "llm_allowed": true,
  "lean_allowed": true,
  "prediction_correct": true,
  "reason": "allowed_by_grant_delete",
  "trace_id": "optional-correlation-id",
  "grant": "delete"
}
```

`grant` is `null` when the policy grants no permission. `lean_allowed` is
computed from LeanACL's `Can` relation. `prediction_correct` is true exactly
when `llm_allowed == lean_allowed`.

## LLM Invocation

The bridge script calls OpenAI Chat Completions over HTTPS using the Python
standard library. It uses OpenAI structured outputs (`response_format` with a
strict JSON schema), so prompts do not need to restate the JSON schema.

Prompts should describe:

- the policy task: decide allow/deny under LeanACL,
- the org/user/resource facts,
- the requested permission,
- any metadata values such as `trace_id` and `prompt_version`.

Environment variables:

- `OPENAI_API_KEY` — required for real LLM calls
- `OPENAI_BASE_URL` — optional, defaults to `https://api.openai.com/v1`
- `OPENAI_MODEL` or `LEANACL_OPENAI_MODEL` — optional, defaults to `gpt-4o-mini`

For offline tests / CI:

- `LEANACL_BRIDGE_LLM_STUB_JSON` — path to a prediction JSON file; when set,
  the bridge returns that file contents for every prompt.
