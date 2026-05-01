import Lean
import LeanACL.Theorems

/-!
# LeanACL.Verify

Command-line verifier for JSON artifacts produced by the Python bridge.

Python owns prompt orchestration and schema normalization. This module checks
an LLM allow/deny prediction against the final ACL decision by constructing
LeanACL terms and evaluating `Can`.
-/

open Lean

namespace LeanACL.Verify

structure JsonMembership where
  orgId : Nat
  role : String
  deriving Repr, FromJson, ToJson

structure JsonUser where
  id : Nat
  memberships : Array JsonMembership
  deriving Repr, FromJson, ToJson

structure JsonResource where
  ownerOrg : Nat
  resourcetype : String
  sensitivity : Bool
  deriving Repr, FromJson, ToJson

structure VerifyRequest where
  trace_id : Option String := none
  prompt_version : Option String := none
  llm_model : Option String := none
  llm_allowed : Bool
  user : JsonUser
  resource : JsonResource
  requested_permission : String
  deriving Repr, FromJson, ToJson

structure Verdict where
  llm_allowed : Bool
  lean_allowed : Bool
  prediction_correct : Bool
  reason : String
  trace_id : Option String
  grant : Option String
  deriving Repr, FromJson, ToJson

def Level.ofString : String -> Except String Level
  | "manager" => .ok .manager
  | "developer" => .ok .developer
  | "devops" => .ok .devops
  | other => .error s!"unknown role: {other}"

def ResourceType.ofString : String -> Except String ResourceType
  | "storage" => .ok .storage
  | "compute" => .ok .compute
  | "data" => .ok .data
  | other => .error s!"unknown resource type: {other}"

def Permission.ofString : String -> Except String Permission
  | "read" => .ok .read
  | "edit" => .ok .edit
  | "delete" => .ok .delete
  | other => .error s!"unknown permission: {other}"

def Permission.toBridgeString : Permission -> String
  | .read => "read"
  | .edit => "edit"
  | .delete => "delete"

def decodeMemberships : List JsonMembership -> Except String (List (Prod OrgId Level))
  | [] => .ok []
  | m :: rest => do
      let role <- Level.ofString m.role
      let decodedRest <- decodeMemberships rest
      return (m.orgId, role) :: decodedRest

def decodeUser (jsonUser : JsonUser) : Except String User := do
  let memberships <- decodeMemberships jsonUser.memberships.toList
  return { id := jsonUser.id, memberships := memberships }

def decodeResource (jsonResource : JsonResource) : Except String Resource := do
  let resourceType <- ResourceType.ofString jsonResource.resourcetype
  return {
    ownerOrg := jsonResource.ownerOrg,
    resourcetype := resourceType,
    sensitivity := jsonResource.sensitivity
  }

structure DecodedRequest where
  trace_id : Option String
  llmAllowed : Bool
  user : User
  resource : Resource
  requestedPermission : Permission

def decodeRequest (request : VerifyRequest) : Except String DecodedRequest := do
  let user <- decodeUser request.user
  let resource <- decodeResource request.resource
  let permission <- Permission.ofString request.requested_permission
  return {
    trace_id := request.trace_id,
    llmAllowed := request.llm_allowed,
    user := user,
    resource := resource,
    requestedPermission := permission
  }

def grantToString (grantValue : Option Permission) : Option String :=
  grantValue.map Permission.toBridgeString

def denialReason (u : User) (r : Resource) (p : Permission) : String :=
  if isSensitiveData r then
    if sameOrg u r then
      "denied_sensitive_data_requires_manager"
    else
      "denied_sensitive_data_requires_same_org_manager"
  else if otherOrg u r && p != .read then
    "denied_cross_org_read_only"
  else
    "denied_no_matching_grant"

def verifyDecoded (request : DecodedRequest) : Verdict :=
  let grantValue := LeanACL.grant request.user request.resource
  let leanAllowed := decide (Can request.user request.resource request.requestedPermission)
  let predictionCorrect := request.llmAllowed == leanAllowed
  let reason :=
    if leanAllowed then
      match grantValue with
      | some p => s!"allowed_by_grant_{Permission.toBridgeString p}"
      | none => "allowed_by_grant"
    else
      denialReason request.user request.resource request.requestedPermission
  {
    llm_allowed := request.llmAllowed,
    lean_allowed := leanAllowed,
    prediction_correct := predictionCorrect,
    reason := reason,
    trace_id := request.trace_id,
    grant := grantToString grantValue
  }

def loadJsonRequest (path : System.FilePath) : IO VerifyRequest := do
  let content <- IO.FS.readFile path
  let json <- match Json.parse content with
    | .ok json => pure json
    | .error err => throw (IO.userError s!"failed to parse JSON: {err}")
  match fromJson? json with
  | .ok request => pure request
  | .error err => throw (IO.userError s!"failed to decode request: {err}")

def verifyFile (inputPath : System.FilePath) : IO Verdict := do
  let request <- loadJsonRequest inputPath
  match decodeRequest request with
  | .ok decoded => pure (verifyDecoded decoded)
  | .error err => throw (IO.userError s!"invalid normalized request: {err}")

def writeVerdict (outputPath : System.FilePath) (verdict : Verdict) : IO Unit := do
  IO.FS.writeFile outputPath (toString (toJson verdict).pretty ++ "\n")

def usage : String :=
  "usage: lake exe leanacl_verify <prediction.json> [verdict.json]"

def main : List String -> IO UInt32
  | [input] => do
      let verdict <- verifyFile input
      IO.println (toJson verdict).pretty
      return 0
  | [input, output] => do
      let verdict <- verifyFile input
      writeVerdict output verdict
      return 0
  | _ => do
      IO.eprintln usage
      return 2

end LeanACL.Verify

def main : List String -> IO UInt32 :=
  LeanACL.Verify.main
