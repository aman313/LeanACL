import LeanACL.Theorems

/-!
# LeanACL.Examples

Concrete scenarios exercising the ACL policy. Each scenario is a `#eval`
witness plus a `decide`-proved theorem, confirming that the decidable
`Can u r p` agrees with our intuitions.

The two mandatory scenarios (per the plan):

1. Same-org developer reading *sensitive* data — **denied**.
2. Same-org manager on *sensitive* data — **granted** (full Delete,
   Edit, Read via grant-closure).

A handful of additional cases round out the coverage of rules 1–10.
-/

namespace LeanACL.Examples

open LeanACL

/-! ## Organizations and users -/

def orgAcme : OrgId := 1
def orgWidgetsCo : OrgId := 2

/-- A same-org manager of Acme. -/
def managerAcme : User :=
  { id := 1, memberships := [(orgAcme, .manager)] }

/-- A same-org developer of Acme. -/
def developerAcme : User :=
  { id := 2, memberships := [(orgAcme, .developer)] }

/-- A same-org devops of Acme. -/
def devopsAcme : User :=
  { id := 3, memberships := [(orgAcme, .devops)] }

/-- A manager of WidgetsCo (i.e., cross-org w.r.t. Acme resources). -/
def managerWidgets : User :=
  { id := 4, memberships := [(orgWidgetsCo, .manager)] }

/-- A developer of WidgetsCo. -/
def developerWidgets : User :=
  { id := 5, memberships := [(orgWidgetsCo, .developer)] }

/-- A devops of WidgetsCo. -/
def devopsWidgets : User :=
  { id := 6, memberships := [(orgWidgetsCo, .devops)] }

/-- A user with a manager role in Acme and a developer role in WidgetsCo. -/
def doubleRole : User :=
  { id := 7, memberships := [(orgAcme, .manager), (orgWidgetsCo, .developer)] }

/-! ## Resources -/

def acmeStorage : Resource :=
  { ownerOrg := orgAcme, resourcetype := .storage, sensitivity := false }

def acmeCompute : Resource :=
  { ownerOrg := orgAcme, resourcetype := .compute, sensitivity := false }

def acmeData : Resource :=
  { ownerOrg := orgAcme, resourcetype := .data, sensitivity := false }

def acmeSensitiveData : Resource :=
  { ownerOrg := orgAcme, resourcetype := .data, sensitivity := true }

/-- Sensitivity on `storage` is semantically inert. Useful for the
sensitivity-irrelevance theorem. -/
def acmeStorageFlagged : Resource :=
  { ownerOrg := orgAcme, resourcetype := .storage, sensitivity := true }

/-! ## Scenario 1 — same-org developer reading *sensitive* data: **denied** -/

/-- A developer in the resource's own org cannot Read sensitive data. -/
example : ¬ Can developerAcme acmeSensitiveData .read := by decide

/-- In fact they have no permission at any level. -/
example : ∀ p : Permission, ¬ Can developerAcme acmeSensitiveData p := by
  intro p
  have hs : isSensitiveData acmeSensitiveData = true := by decide
  have hnmgr : hasRoleIn developerAcme acmeSensitiveData.ownerOrg .manager = false := by decide
  exact not_Can_sensitive_sameOrg_nonManager _ _ hs hnmgr p

/-- Same for same-org devops: blocked on sensitive data. -/
example : ¬ Can devopsAcme acmeSensitiveData .read := by decide

/-! ## Scenario 2 — same-org manager on *sensitive* data: full access -/

example : Can managerAcme acmeSensitiveData .delete := by decide
example : Can managerAcme acmeSensitiveData .edit := by decide
example : Can managerAcme acmeSensitiveData .read := by decide

/-! ## Rule 1 — same-org any user can Read -/

example : Can developerAcme acmeStorage .read := by decide
example : Can developerAcme acmeData .read := by decide
example : Can devopsAcme acmeData .read := by decide

/-! ## Rule 2 — same-org manager can Edit data -/

example : Can managerAcme acmeData .edit := by decide
/-- …but not devops in the same org (devops only edits storage/compute). -/
example : ¬ Can devopsAcme acmeData .edit := by decide

/-! ## Rule 3 — same-org devops can Edit storage/compute -/

example : Can devopsAcme acmeStorage .edit := by decide
example : Can devopsAcme acmeCompute .edit := by decide

/-! ## Rule 4 — grant-closure -/

example : Can managerAcme acmeData .read := Can.delete_to_read (by decide)
example : Can devopsAcme acmeStorage .read := Can.edit_to_read (by decide)

/-! ## Rule 5 — cross-org manager can Read -/

example : Can managerWidgets acmeStorage .read := by decide
example : Can managerWidgets acmeData .read := by decide
/-- …but only Read, never Edit. -/
example : ¬ Can managerWidgets acmeData .edit := by decide

/-! ## Rule 6 — cross-org developer can Read data only -/

example : Can developerWidgets acmeData .read := by decide
example : ¬ Can developerWidgets acmeStorage .read := by decide
example : ¬ Can developerWidgets acmeCompute .read := by decide

/-! ## Rule 7 — cross-org devops can Read storage/compute only -/

example : Can devopsWidgets acmeStorage .read := by decide
example : Can devopsWidgets acmeCompute .read := by decide
example : ¬ Can devopsWidgets acmeData .read := by decide

/-! ## Rule 8 — same-org devops can Delete storage/compute -/

example : Can devopsAcme acmeStorage .delete := by decide
example : Can devopsAcme acmeCompute .delete := by decide
/-- …but not data. -/
example : ¬ Can devopsAcme acmeData .delete := by decide

/-! ## Rule 9 — same-org manager can Delete data -/

example : Can managerAcme acmeData .delete := by decide

/-! ## Rule 10 — sensitive data lockdown -/

example : ¬ Can developerAcme acmeSensitiveData .read := by decide
example : ¬ Can devopsAcme acmeSensitiveData .read := by decide
example : ¬ Can managerWidgets acmeSensitiveData .read := by decide
example : Can managerAcme acmeSensitiveData .delete := by decide

/-! ## Multi-role users -/

example : Can doubleRole acmeData .delete := by decide
example : Can doubleRole acmeSensitiveData .delete := by decide

/-! ## Sensitivity irrelevance on non-data -/

/-- Storage with `sensitivity = true` behaves like storage with
`sensitivity = false`: the sensitivity flag is ignored. -/
example : Can developerAcme acmeStorageFlagged .read ↔
          Can developerAcme acmeStorage .read :=
  Iff.symm (Can_sensitivity_irrelevant_non_data _ _ _ (by decide) _)

/-! ## Membership monotonicity -/

/-- Adding a manager role in WidgetsCo to `developerAcme` only *adds* powers. -/
example :
    Can developerAcme acmeData .read →
    Can { developerAcme with memberships := (orgWidgetsCo, .manager) ::
      developerAcme.memberships } acmeData .read :=
  Can_role_addition_mono _ _ _ _ _

end LeanACL.Examples
