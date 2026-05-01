import LeanACL.Terms
import Mathlib.Tactic

/-!
# LeanACL.Access

Predicates (`sameOrg`, `hasRoleIn`, …), the policy `grant`, the access
relation `Can`, and the inductive spec `Derivable` together with the
`Can ↔ Derivable` equivalence.

The model is **deny-override with default deny**:

* `grantOpen` computes the strongest permission granted by rules 1–9.
* `grantSensitive` handles rule 10 (sensitive-data manager-only override).
* `grant` dispatches between the two at the top level; any other rule's
  contribution on sensitive data is discarded.

Each of the four contributions to `grantOpen` is exposed as a named
top-level `def` (`sameDeletePart`, `sameEditPart`, `sameReadPart`,
`crossReadPart`) to make rule-by-rule proofs tractable.
-/

namespace LeanACL

/-! ## Predicates -/

/-- `u` belongs to the org that owns `r`. -/
def sameOrg (u : User) (r : Resource) : Bool :=
  u.memberships.any (fun m => m.fst == r.ownerOrg)

/-- `u` is a member of org `o` with role `l`. -/
def hasRoleIn (u : User) (o : OrgId) (l : Level) : Bool :=
  u.memberships.any (fun m => m.fst == o && m.snd == l)

/-- Canonical dual of `sameOrg`. **Never** redefine — use this alias. -/
def otherOrg (u : User) (r : Resource) : Bool := !sameOrg u r

/-- `u` has role `l` in at least one of their orgs. Used by cross-org read
rules (5–7) which fire whenever the user has the relevant role *anywhere*. -/
def hasRoleAnywhere (u : User) (l : Level) : Bool :=
  u.memberships.any (fun m => m.snd == l)

/-- Resource is both `data` and flagged sensitive. Triggers rule 10. -/
def isSensitiveData (r : Resource) : Bool :=
  match r.resourcetype with
  | .data => r.sensitivity
  | _     => false

/-! `otherOrg` is definitionally just boolean negation of `sameOrg`. -/
theorem otherOrg_eq (u : User) (r : Resource) :
    otherOrg u r = !sameOrg u r := rfl

/-- Boolean equivalence used to switch between `otherOrg = true` and `sameOrg = false`. -/
theorem otherOrg_true_iff_sameOrg_false (u : User) (r : Resource) :
    otherOrg u r = true ↔ sameOrg u r = false := by
  unfold otherOrg; cases sameOrg u r <;> simp

/-- Forward direction of the org-duality check: cross-org implies not same-org. -/
theorem not_sameOrg_of_otherOrg {u : User} {r : Resource} (h : otherOrg u r = true) :
    sameOrg u r = false := (otherOrg_true_iff_sameOrg_false u r).mp h

/-- Reverse direction of the org-duality check: not same-org implies cross-org. -/
theorem otherOrg_of_not_sameOrg {u : User} {r : Resource} (h : sameOrg u r = false) :
    otherOrg u r = true := (otherOrg_true_iff_sameOrg_false u r).mpr h

/-- If the resource is not `data`, then `isSensitiveData` is `false`. -/
theorem isSensitiveData_of_not_data (r : Resource) (h : r.resourcetype ≠ .data) :
    isSensitiveData r = false := by
  unfold isSensitiveData
  split
  · next heq => exact absurd heq h
  · rfl

/-- If the resource is not `data`, `isSensitiveData` is `false` regardless of
`sensitivity`. Used by the sensitivity-irrelevance theorem. -/
@[simp] theorem isSensitiveData_of_not_data_any (o : OrgId) (rt : ResourceType)
    (hrt : rt ≠ .data) (b : Bool) :
    isSensitiveData { ownerOrg := o, resourcetype := rt, sensitivity := b } = false := by
  unfold isSensitiveData
  cases rt <;> simp_all

/-! ## Option max helper -/

/-- Join `Option Permission` values, treating `none` as bottom. -/
def Option.mergePerm : Option Permission → Option Permission → Option Permission
  | none,     y        => y
  | x,        none     => x
  | some a,   some b   => some (Permission.max a b)

/-- Identity check for merge with `none` on the left. -/
@[simp] theorem Option.mergePerm_none_left (y : Option Permission) :
    Option.mergePerm none y = y := rfl

/-- Identity check for merge with `none` on the right. -/
@[simp] theorem Option.mergePerm_none_right (x : Option Permission) :
    Option.mergePerm x none = x := by cases x <;> rfl

/-- Merge behavior check when both inputs are present. -/
@[simp] theorem Option.mergePerm_some_some (a b : Permission) :
    Option.mergePerm (some a) (some b) = some (Permission.max a b) := rfl

/-- Check that a left-side witness `x = some v` with `p ≤ v` survives merging. -/
theorem Option.mergePerm_preserves_ge_left {x y : Option Permission} {p v : Permission}
    (hx : x = some v) (hpv : p ≤ v) :
    ∃ w, Option.mergePerm x y = some w ∧ p ≤ w := by
  subst hx
  cases y with
  | none => exact ⟨v, rfl, hpv⟩
  | some b =>
    refine ⟨Permission.max v b, rfl, ?_⟩
    exact Permission.le_trans hpv (Permission.le_max_left v b)

/-- Check that a right-side witness `y = some v` with `p ≤ v` survives merging. -/
theorem Option.mergePerm_preserves_ge_right {x y : Option Permission} {p v : Permission}
    (hy : y = some v) (hpv : p ≤ v) :
    ∃ w, Option.mergePerm x y = some w ∧ p ≤ w := by
  subst hy
  cases x with
  | none => exact ⟨v, rfl, hpv⟩
  | some a =>
    refine ⟨Permission.max a v, rfl, ?_⟩
    exact Permission.le_trans hpv (Permission.le_max_right a v)

/-- Monotonicity check for merge in its left input (existential witness form). -/
theorem Option.mergePerm_mono_left {x y : Option Permission} {p : Permission}
    (hx : ∃ v, x = some v ∧ p ≤ v) :
    ∃ w, Option.mergePerm x y = some w ∧ p ≤ w := by
  obtain ⟨v, hx, hpv⟩ := hx
  exact Option.mergePerm_preserves_ge_left hx hpv

/-- Monotonicity check for merge in its right input (existential witness form). -/
theorem Option.mergePerm_mono_right {x y : Option Permission} {p : Permission}
    (hy : ∃ v, y = some v ∧ p ≤ v) :
    ∃ w, Option.mergePerm x y = some w ∧ p ≤ w := by
  obtain ⟨v, hy, hpv⟩ := hy
  exact Option.mergePerm_preserves_ge_right hy hpv

/-- Inverse: if merge yields `some q`, one of the inputs is `some q` (since
`Permission.max` always equals one of its arguments). -/
theorem Option.mergePerm_eq_some_or {x y : Option Permission} {q : Permission} :
    Option.mergePerm x y = some q → x = some q ∨ y = some q := by
  intro h
  cases x with
  | none =>
    right
    simpa using h
  | some a =>
    cases y with
    | none =>
      left
      simpa using h
    | some b =>
      simp only [Option.mergePerm_some_some, Permission.max] at h
      split at h
      · right; exact congrArg some (Option.some.inj h)
      · left;  exact congrArg some (Option.some.inj h)

/-! ## The four grant contributors (rules 1–9) -/

/-- Rules 8 & 9: same-org `Delete`. -/
def sameDeletePart (u : User) (r : Resource) : Option Permission :=
  if sameOrg u r = true ∧
     ((hasRoleIn u r.ownerOrg .devops  = true ∧ r.resourcetype ≠ .data) ∨
      (hasRoleIn u r.ownerOrg .manager = true ∧ r.resourcetype = .data))
  then some .delete else none

/-- Rules 2 & 3: same-org `Edit`. -/
def sameEditPart (u : User) (r : Resource) : Option Permission :=
  if sameOrg u r = true ∧
     ((hasRoleIn u r.ownerOrg .manager = true ∧ r.resourcetype = .data) ∨
      (hasRoleIn u r.ownerOrg .devops  = true ∧ r.resourcetype ≠ .data))
  then some .edit else none

/-- Rule 1: same-org `Read`. -/
def sameReadPart (u : User) (r : Resource) : Option Permission :=
  if sameOrg u r = true then some .read else none

/-- Rules 5, 6, 7: cross-org `Read`. -/
def crossReadPart (u : User) (r : Resource) : Option Permission :=
  if otherOrg u r = true ∧
     (hasRoleAnywhere u .manager = true ∨
      (r.resourcetype = .data  ∧ hasRoleAnywhere u .developer = true) ∨
      (r.resourcetype ≠ .data  ∧ hasRoleAnywhere u .devops    = true))
  then some .read else none

/-! ## The policy -/

/-- Open-world part of the policy: rules 1–9, combined by `max`. -/
def grantOpen (u : User) (r : Resource) : Option Permission :=
  Option.mergePerm
    (Option.mergePerm
      (Option.mergePerm (sameDeletePart u r) (sameEditPart u r))
      (sameReadPart u r))
    (crossReadPart u r)

/-- Rule 10: on sensitive data, only same-org managers have access.
We pin the grant to `.delete` so grant-closure gives them Edit & Read. -/
def grantSensitive (u : User) (r : Resource) : Option Permission :=
  if sameOrg u r = true ∧ hasRoleIn u r.ownerOrg .manager = true
  then some .delete else none

/-- The whole policy. Deny-override: sensitive-data branch wins. -/
def grant (u : User) (r : Resource) : Option Permission :=
  if isSensitiveData r = true then grantSensitive u r else grantOpen u r

/-! ## `Can`, weakening, decidability -/

/-- `Can u r p` — user `u` is permitted permission `p` on resource `r` by the
policy. Downward closure (rule 4) of the top permission returned by `grant`. -/
def Can (u : User) (r : Resource) (p : Permission) : Prop :=
  ∃ q, grant u r = some q ∧ p ≤ q

instance canDecidable (u : User) (r : Resource) (p : Permission) : Decidable (Can u r p) :=
  match hg : grant u r with
  | none =>
    isFalse fun ⟨_, hq, _⟩ => by rw [hg] at hq; contradiction
  | some v =>
    if hle : p ≤ v then
      isTrue ⟨v, hg, hle⟩
    else
      isFalse fun ⟨_, hq, hqv⟩ => by
        rw [hg] at hq
        exact hle (by cases hq; exact hqv)

/-- Rule 4 as a theorem: permission weakening. -/
theorem Can.weaken {u : User} {r : Resource} {p q : Permission}
    (hpq : p ≤ q) (hq : Can u r q) : Can u r p := by
  obtain ⟨v, hv, hqv⟩ := hq
  exact ⟨v, hv, Permission.le_trans hpq hqv⟩

/-- Rule-4 helper check: `delete` access implies `edit` access. -/
theorem Can.delete_to_edit {u r} (h : Can u r .delete) : Can u r .edit :=
  Can.weaken Permission.edit_le_delete h

/-- Rule-4 helper check: `edit` access implies `read` access. -/
theorem Can.edit_to_read {u r} (h : Can u r .edit) : Can u r .read :=
  Can.weaken Permission.read_le_edit h

/-- Rule-4 helper check: `delete` access implies `read` access. -/
theorem Can.delete_to_read {u r} (h : Can u r .delete) : Can u r .read :=
  Can.weaken Permission.read_le_delete h

/-- Closed-world: if nothing is granted, nothing is permitted. -/
theorem Can.of_grant_none {u r} (h : grant u r = none) (p : Permission) :
    ¬ Can u r p := by
  rintro ⟨_, hq, _⟩
  rw [h] at hq
  contradiction

/-! ## `Derivable` — the inductive spec view

One constructor per English rule. Every rule that would be *suppressed* by
rule 10 on sensitive data carries an explicit `isSensitiveData r = false`
premise. Rule 10 itself has its own constructor.
-/

inductive Derivable : User → Resource → Permission → Prop where
  /-- Rule 1: same-org users read any resource in the org (unless sensitive). -/
  | rule1 {u r} : sameOrg u r = true → isSensitiveData r = false →
      Derivable u r .read
  /-- Rule 2: manager + data + same org → edit. -/
  | rule2 {u r} : sameOrg u r = true → hasRoleIn u r.ownerOrg .manager = true →
      r.resourcetype = .data → Derivable u r .edit
  /-- Rule 3: devops + non-data + same org → edit. -/
  | rule3 {u r} : sameOrg u r = true → hasRoleIn u r.ownerOrg .devops = true →
      r.resourcetype ≠ .data → Derivable u r .edit
  /-- Rule 4: permission weakening / grant-closure. -/
  | weaken {u r p q} : p ≤ q → Derivable u r q → Derivable u r p
  /-- Rule 5: manager can read any resource in any org (unless sensitive). -/
  | rule5 {u r} : hasRoleAnywhere u .manager = true → isSensitiveData r = false →
      Derivable u r .read
  /-- Rule 6: developer + data cross-org → read (unless sensitive). -/
  | rule6 {u r} : otherOrg u r = true → hasRoleAnywhere u .developer = true →
      r.resourcetype = .data → isSensitiveData r = false →
      Derivable u r .read
  /-- Rule 7: devops + non-data cross-org → read. -/
  | rule7 {u r} : otherOrg u r = true → hasRoleAnywhere u .devops = true →
      r.resourcetype ≠ .data → Derivable u r .read
  /-- Rule 8: devops + non-data + same org → delete. -/
  | rule8 {u r} : sameOrg u r = true → hasRoleIn u r.ownerOrg .devops = true →
      r.resourcetype ≠ .data → Derivable u r .delete
  /-- Rule 9: manager + data + same org → delete. -/
  | rule9 {u r} : sameOrg u r = true → hasRoleIn u r.ownerOrg .manager = true →
      r.resourcetype = .data → Derivable u r .delete
  /-- Rule 10: sensitive-data override — only same-org managers. -/
  | rule10 {u r} : isSensitiveData r = true → sameOrg u r = true →
      hasRoleIn u r.ownerOrg .manager = true → Derivable u r .delete

/-! ## Soundness: `Derivable → Can`

Strategy: for each constructor, exhibit a contributor of `grant` that fires at
the required permission level; merge monotonicity lifts the bound to the top. -/

section Soundness

variable {u : User} {r : Resource}

/-- Non-sensitive ⇒ grant = grantOpen. -/
private theorem grant_open_of_nonsens (hns : isSensitiveData r = false) :
    grant u r = grantOpen u r := by
  unfold grant; rw [if_neg (by simp [hns])]

/-- Sensitive ⇒ grant = grantSensitive. -/
private theorem grant_sensitive_of_sens (hs : isSensitiveData r = true) :
    grant u r = grantSensitive u r := by
  unfold grant; rw [if_pos (by simp [hs])]

/-- Lift a part's lower bound to `grantOpen` via nested merges. -/
private theorem can_of_part_sameDelete (hns : isSensitiveData r = false)
    (hpart : ∃ v, sameDeletePart u r = some v ∧ .delete ≤ v) :
    Can u r .delete := by
  rw [Can, grant_open_of_nonsens hns, grantOpen]
  exact Option.mergePerm_mono_left (Option.mergePerm_mono_left (Option.mergePerm_mono_left hpart))

private theorem can_of_part_sameEdit (hns : isSensitiveData r = false)
    (hpart : ∃ v, sameEditPart u r = some v ∧ .edit ≤ v) :
    Can u r .edit := by
  rw [Can, grant_open_of_nonsens hns, grantOpen]
  exact Option.mergePerm_mono_left (Option.mergePerm_mono_left (Option.mergePerm_mono_right hpart))

private theorem can_of_part_sameRead (hns : isSensitiveData r = false)
    (hpart : ∃ v, sameReadPart u r = some v ∧ .read ≤ v) :
    Can u r .read := by
  rw [Can, grant_open_of_nonsens hns, grantOpen]
  exact Option.mergePerm_mono_left (Option.mergePerm_mono_right hpart)

private theorem can_of_part_crossRead (hns : isSensitiveData r = false)
    (hpart : ∃ v, crossReadPart u r = some v ∧ .read ≤ v) :
    Can u r .read := by
  rw [Can, grant_open_of_nonsens hns, grantOpen]
  exact Option.mergePerm_mono_right hpart

private theorem can_of_grantSensitive (hs : isSensitiveData r = true)
    (hpart : ∃ v, grantSensitive u r = some v ∧ .delete ≤ v) :
    Can u r .delete := by
  rw [Can, grant_sensitive_of_sens hs]
  exact hpart

/-- If resource is `data`, sensitivity decides `isSensitiveData`. -/
private theorem isSensitiveData_data_iff {r : Resource} (hdata : r.resourcetype = .data) :
    isSensitiveData r = r.sensitivity := by
  unfold isSensitiveData; rw [hdata]

/-- Soundness check of the declarative rules against the executable policy. -/
theorem Derivable.sound : ∀ {u r p}, Derivable u r p → Can u r p := by
  intro u r p h
  induction h with
  | rule1 hso hns =>
    exact can_of_part_sameRead hns ⟨.read, by unfold sameReadPart; simp [hso], Permission.le_refl _⟩
  | rule2 hso hmgr hdata =>
    -- Case on sensitivity: rule 2 still holds on sensitive data via rule 10 + closure.
    by_cases hs : isSensitiveData r = true
    · -- sensitive → grant = some .delete; .edit ≤ .delete
      refine Can.weaken Permission.edit_le_delete ?_
      apply can_of_grantSensitive hs
      refine ⟨.delete, ?_, Permission.le_refl _⟩
      unfold grantSensitive; simp [hso, hmgr]
    · have hns : isSensitiveData r = false := by
        cases h : isSensitiveData r
        · rfl
        · exact absurd h hs
      apply can_of_part_sameEdit hns
      refine ⟨.edit, ?_, Permission.le_refl _⟩
      unfold sameEditPart; simp [hso, hmgr, hdata]
  | rule3 hso hdev hrt =>
    have hns : isSensitiveData r = false := isSensitiveData_of_not_data r hrt
    apply can_of_part_sameEdit hns
    refine ⟨.edit, ?_, Permission.le_refl _⟩
    unfold sameEditPart
    simp [hso, hdev, hrt]
  | weaken hpq _ ih => exact ih.weaken hpq
  | rule5 hmgr hns =>
    by_cases hso : sameOrg u r = true
    · apply can_of_part_sameRead hns
      refine ⟨.read, ?_, Permission.le_refl _⟩
      unfold sameReadPart; simp [hso]
    · have hsofalse : sameOrg u r = false := by
        cases h : sameOrg u r
        · rfl
        · exact absurd h hso
      have hother : otherOrg u r = true := otherOrg_of_not_sameOrg hsofalse
      apply can_of_part_crossRead hns
      refine ⟨.read, ?_, Permission.le_refl _⟩
      unfold crossReadPart
      simp [hother, hmgr]
  | rule6 hother hdev hdata hns =>
    apply can_of_part_crossRead hns
    refine ⟨.read, ?_, Permission.le_refl _⟩
    unfold crossReadPart
    simp [hother, hdev, hdata]
  | rule7 hother hdev hrt =>
    have hns : isSensitiveData r = false := isSensitiveData_of_not_data r hrt
    apply can_of_part_crossRead hns
    refine ⟨.read, ?_, Permission.le_refl _⟩
    unfold crossReadPart
    simp [hother, hdev, hrt]
  | rule8 hso hdev hrt =>
    have hns : isSensitiveData r = false := isSensitiveData_of_not_data r hrt
    apply can_of_part_sameDelete hns
    refine ⟨.delete, ?_, Permission.le_refl _⟩
    unfold sameDeletePart
    simp [hso, hdev, hrt]
  | rule9 hso hmgr hdata =>
    by_cases hs : isSensitiveData r = true
    · apply can_of_grantSensitive hs
      refine ⟨.delete, ?_, Permission.le_refl _⟩
      unfold grantSensitive; simp [hso, hmgr]
    · have hns : isSensitiveData r = false := by
        cases h : isSensitiveData r
        · rfl
        · exact absurd h hs
      apply can_of_part_sameDelete hns
      refine ⟨.delete, ?_, Permission.le_refl _⟩
      unfold sameDeletePart
      simp [hso, hmgr, hdata]
  | rule10 hs hso hmgr =>
    apply can_of_grantSensitive hs
    refine ⟨.delete, ?_, Permission.le_refl _⟩
    unfold grantSensitive; simp [hso, hmgr]

end Soundness

/-! ## Completeness: `Can → Derivable`

Strategy: unpack `Can` to `grant u r = some q ∧ p ≤ q`. Case on sensitivity:

* Sensitive: `grantSensitive` returns `some .delete` iff `sameOrg ∧ manager`.
  Apply rule 10, weaken to `p`.
* Non-sensitive: `grantOpen` is a chain of three merges. Repeatedly apply
  `mergePerm_eq_some_or` to isolate which contributor fired, then dispatch
  to the matching rule. -/

section Completeness

variable {u : User} {r : Resource}

/-- Helper: if a non-sensitive resource's `sameDeletePart` produced `some q`,
then q must be `.delete` and rules 8 or 9 apply. -/
private theorem derivable_of_sameDeletePart {q : Permission}
    (h : sameDeletePart u r = some q) :
    Derivable u r q := by
  unfold sameDeletePart at h
  split at h
  · rename_i hall
    obtain ⟨hso, hcond⟩ := hall
    have hqd : q = .delete := by cases h; rfl
    subst hqd
    rcases hcond with ⟨hdev, hrt⟩ | ⟨hmgr, hrt⟩
    · exact .rule8 hso hdev hrt
    · exact .rule9 hso hmgr hrt
  · contradiction

private theorem derivable_of_sameEditPart {q : Permission}
    (h : sameEditPart u r = some q) :
    Derivable u r q := by
  unfold sameEditPart at h
  split at h
  · rename_i hall
    obtain ⟨hso, hcond⟩ := hall
    have hqe : q = .edit := by cases h; rfl
    subst hqe
    rcases hcond with ⟨hmgr, hrt⟩ | ⟨hdev, hrt⟩
    · exact .rule2 hso hmgr hrt
    · exact .rule3 hso hdev hrt
  · contradiction

private theorem derivable_of_sameReadPart {q : Permission}
    (h : sameReadPart u r = some q) (hns : isSensitiveData r = false) :
    Derivable u r q := by
  unfold sameReadPart at h
  split at h
  · rename_i hso
    have hqr : q = .read := by cases h; rfl
    subst hqr
    exact .rule1 hso hns
  · contradiction

private theorem derivable_of_crossReadPart {q : Permission}
    (h : crossReadPart u r = some q) (hns : isSensitiveData r = false) :
    Derivable u r q := by
  unfold crossReadPart at h
  split at h
  · rename_i hall
    obtain ⟨hother, hcond⟩ := hall
    have hqr : q = .read := by cases h; rfl
    subst hqr
    rcases hcond with hmgr | ⟨hdata, hdev⟩ | ⟨hrt, hdvo⟩
    · exact .rule5 hmgr hns
    · exact .rule6 hother hdev hdata hns
    · exact .rule7 hother hdvo hrt
  · contradiction

/-- Completeness check of the declarative rules against the executable policy. -/
theorem Derivable.complete {u r p} : Can u r p → Derivable u r p := by
  rintro ⟨q, hg, hpq⟩
  by_cases hs : isSensitiveData r = true
  · rw [grant_sensitive_of_sens hs] at hg
    unfold grantSensitive at hg
    split at hg
    · rename_i hall
      obtain ⟨hso, hmgr⟩ := hall
      have hqd : q = .delete := by cases hg; rfl
      subst hqd
      exact .weaken hpq (.rule10 hs hso hmgr)
    · contradiction
  · have hns : isSensitiveData r = false := by
      cases h : isSensitiveData r
      · rfl
      · exact absurd h hs
    rw [grant_open_of_nonsens hns] at hg
    unfold grantOpen at hg
    rcases Option.mergePerm_eq_some_or hg with h1 | hcross
    · rcases Option.mergePerm_eq_some_or h1 with h2 | hread
      · rcases Option.mergePerm_eq_some_or h2 with hdel | hedit
        · exact .weaken hpq (derivable_of_sameDeletePart hdel)
        · exact .weaken hpq (derivable_of_sameEditPart hedit)
      · exact .weaken hpq (derivable_of_sameReadPart hread hns)
    · exact .weaken hpq (derivable_of_crossReadPart hcross hns)

end Completeness

/-- The marquee equivalence: computational policy = declarative spec. -/
theorem Can_iff_Derivable (u : User) (r : Resource) (p : Permission) :
    Can u r p ↔ Derivable u r p :=
  ⟨Derivable.complete, Derivable.sound⟩

end LeanACL
