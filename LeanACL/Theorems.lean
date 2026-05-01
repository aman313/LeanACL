import LeanACL.Access

/-!
# LeanACL.Theorems

Formal security properties of the ACL policy. Organised by the tiers in the
plan:

* Tier 1 — **spec-critical**: Delete characterization, Sensitive lockdown,
  Sensitivity irrelevance for non-data, Role non-escalation, Cross-org denial,
  Closed-world witness, Rule subsumption.
* Tier 2 — **structural**: weakening / grant-closure (already in `Access`),
  decidability.
* Tier 3 — **frame and monotonicity**: adding users / memberships is monotone;
  flipping `sensitivity` false → true is *anti-monotone* (the only such axis).
* Tier 4 — **sanity**: consistency, idempotence under reorder/dup.
-/

namespace LeanACL

/-! ## Utility lemmas -/

/-- The only way to reach `.delete` on the permission chain. -/
theorem Permission.delete_le_iff_eq {q : Permission} : .delete ≤ q ↔ q = .delete := by
  constructor
  · intro h; exact Permission.le_antisymm (Permission.le_delete q) h
  · rintro rfl; exact Permission.le_refl _

/-- Merging `some .delete` on the left always yields `some .delete`. -/
theorem Option.mergePerm_delete_left (y : Option Permission) :
    Option.mergePerm (some Permission.delete) y = some Permission.delete := by
  cases y with
  | none => rfl
  | some v =>
    show some (Permission.max Permission.delete v) = some Permission.delete
    congr 1
    unfold Permission.max
    split
    · rename_i hle
      exact Permission.le_antisymm (Permission.le_delete v) hle
    · rfl

/-- Merging `some .delete` on the right always yields `some .delete`. -/
theorem Option.mergePerm_delete_right (x : Option Permission) :
    Option.mergePerm x (some Permission.delete) = some Permission.delete := by
  cases x with
  | none => rfl
  | some v =>
    show some (Permission.max v Permission.delete) = some Permission.delete
    congr 1
    unfold Permission.max
    split
    · rfl
    · exact absurd (Permission.le_delete v) ‹_›

/-- `sameEditPart` always produces `some .edit` or `none`. -/
theorem sameEditPart_eq (u : User) (r : Resource) :
    sameEditPart u r = some .edit ∨ sameEditPart u r = none := by
  unfold sameEditPart
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `sameReadPart` always produces `some .read` or `none`. -/
theorem sameReadPart_eq (u : User) (r : Resource) :
    sameReadPart u r = some .read ∨ sameReadPart u r = none := by
  unfold sameReadPart
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `crossReadPart` always produces `some .read` or `none`. -/
theorem crossReadPart_eq (u : User) (r : Resource) :
    crossReadPart u r = some .read ∨ crossReadPart u r = none := by
  unfold crossReadPart
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `sameDeletePart` always produces `some .delete` or `none`. -/
theorem sameDeletePart_eq (u : User) (r : Resource) :
    sameDeletePart u r = some .delete ∨ sameDeletePart u r = none := by
  unfold sameDeletePart
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `grantOpen u r = some .delete ↔ sameDeletePart u r = some .delete`.
Non-delete parts max out at `.edit` or `.read`, strictly below `.delete`. -/
theorem grantOpen_eq_some_delete_iff (u : User) (r : Resource) :
    grantOpen u r = some .delete ↔ sameDeletePart u r = some .delete := by
  constructor
  · intro hg
    unfold grantOpen at hg
    rcases Option.mergePerm_eq_some_or hg with h1 | hcross
    · rcases Option.mergePerm_eq_some_or h1 with h2 | hread
      · rcases Option.mergePerm_eq_some_or h2 with hdel | hedit
        · exact hdel
        · rcases sameEditPart_eq u r with he | he
          · rw [he] at hedit; exact absurd hedit (by decide)
          · rw [he] at hedit; contradiction
      · rcases sameReadPart_eq u r with hr | hr
        · rw [hr] at hread; exact absurd hread (by decide)
        · rw [hr] at hread; contradiction
    · rcases crossReadPart_eq u r with hr | hr
      · rw [hr] at hcross; exact absurd hcross (by decide)
      · rw [hr] at hcross; contradiction
  · intro hsd
    unfold grantOpen
    rw [hsd]
    simp only [Option.mergePerm_delete_left]

/-! ## Tier 1.2 — Delete characterization -/

/-- Delete characterization on non-sensitive resources. -/
theorem Can_delete_iff_nonSensitive (u : User) (r : Resource)
    (hns : isSensitiveData r = false) :
    Can u r .delete ↔
      sameOrg u r = true ∧
      ((hasRoleIn u r.ownerOrg .devops  = true ∧ r.resourcetype ≠ .data) ∨
       (hasRoleIn u r.ownerOrg .manager = true ∧ r.resourcetype = .data)) := by
  constructor
  · rintro ⟨q, hg, hpq⟩
    have hqd : q = .delete := Permission.delete_le_iff_eq.mp hpq
    subst hqd
    unfold grant at hg
    rw [if_neg (by simp [hns])] at hg
    have hsd : sameDeletePart u r = some .delete :=
      (grantOpen_eq_some_delete_iff u r).mp hg
    unfold sameDeletePart at hsd
    split at hsd
    · rename_i hall; exact hall
    · contradiction
  · rintro ⟨hso, hcond⟩
    rcases hcond with ⟨hdev, hrt⟩ | ⟨hmgr, hrt⟩
    · exact (Derivable.rule8 hso hdev hrt).sound
    · exact (Derivable.rule9 hso hmgr hrt).sound

/-- Delete characterization on sensitive resources. -/
theorem Can_delete_iff_sensitive (u : User) (r : Resource)
    (hs : isSensitiveData r = true) :
    Can u r .delete ↔
      sameOrg u r = true ∧ hasRoleIn u r.ownerOrg .manager = true := by
  constructor
  · rintro ⟨q, hg, hpq⟩
    have hqd : q = .delete := Permission.delete_le_iff_eq.mp hpq
    subst hqd
    unfold grant at hg
    rw [if_pos (by simp [hs])] at hg
    unfold grantSensitive at hg
    split at hg
    · rename_i hall; exact hall
    · contradiction
  · rintro ⟨hso, hmgr⟩
    exact (Derivable.rule10 hs hso hmgr).sound

/-! ## Tier 1.3 — Sensitive lockdown -/

/-- On sensitive data, any access requires same-org + manager. -/
theorem Can_of_sensitive (u : User) (r : Resource) (p : Permission)
    (hs : isSensitiveData r = true) :
    Can u r p ↔ sameOrg u r = true ∧ hasRoleIn u r.ownerOrg .manager = true := by
  constructor
  · rintro ⟨q, hg, _⟩
    unfold grant at hg
    rw [if_pos (by simp [hs])] at hg
    unfold grantSensitive at hg
    split at hg
    · rename_i hall; exact hall
    · contradiction
  · rintro ⟨hso, hmgr⟩
    refine Can.weaken (Permission.le_delete p) ?_
    exact (Derivable.rule10 hs hso hmgr).sound

/-- Sensitive data + same-org + ¬ manager ⇒ no access at any level.
Same-org developers / devops are fully blocked on sensitive data. -/
theorem not_Can_sensitive_sameOrg_nonManager (u : User) (r : Resource)
    (hs : isSensitiveData r = true)
    (hnmgr : hasRoleIn u r.ownerOrg .manager = false) (p : Permission) :
    ¬ Can u r p := by
  rw [Can_of_sensitive u r p hs]
  rintro ⟨_, hmgr⟩
  rw [hnmgr] at hmgr
  exact Bool.false_ne_true hmgr

/-- Sensitive data + cross-org ⇒ no read access, even for managers anywhere else. -/
theorem not_Can_sensitive_otherOrg (u : User) (r : Resource)
    (hs : isSensitiveData r = true)
    (hother : otherOrg u r = true) :
    ¬ Can u r .read := by
  rw [Can_of_sensitive u r .read hs]
  rintro ⟨hso, _⟩
  have : sameOrg u r = false := not_sameOrg_of_otherOrg hother
  rw [this] at hso
  exact Bool.false_ne_true hso

/-! ## Tier 1.4 — Sensitivity irrelevance for non-data -/

/-- If the resource is not `data`, flipping `sensitivity` never changes `Can`.
This formally justifies carrying `sensitivity` on every `Resource`. -/
theorem Can_sensitivity_irrelevant_non_data (u : User) (r : Resource) (p : Permission)
    (hrt : r.resourcetype ≠ .data) (b : Bool) :
    Can u r p ↔ Can u { r with sensitivity := b } p := by
  have hns_r : isSensitiveData r = false := isSensitiveData_of_not_data r hrt
  have hns_b : isSensitiveData { r with sensitivity := b } = false :=
    isSensitiveData_of_not_data _ hrt
  have hgrant_eq : grant u r = grant u { r with sensitivity := b } := by
    unfold grant
    rw [if_neg (by simp [hns_r]), if_neg (by simp [hns_b])]
    rfl
  unfold Can
  rw [hgrant_eq]

/-! ## Tier 1.5 — Role non-escalation -/

/-- A pure developer (no manager nor devops role anywhere) can only ever read. -/
theorem Can_pure_developer (u : User) (r : Resource) (p : Permission)
    (hnm : ∀ o, hasRoleIn u o .manager = false)
    (hnd : ∀ o, hasRoleIn u o .devops  = false)
    (hpne : p ≠ .read) : ¬ Can u r p := by
  have hnam : hasRoleAnywhere u .manager = false := by
    unfold hasRoleAnywhere
    rw [List.any_eq_false]
    intro ⟨o, l⟩ hmem
    specialize hnm o
    unfold hasRoleIn at hnm
    rw [List.any_eq_false] at hnm
    have := hnm (o, l) hmem
    simpa using this
  have hnad : hasRoleAnywhere u .devops = false := by
    unfold hasRoleAnywhere
    rw [List.any_eq_false]
    intro ⟨o, l⟩ hmem
    specialize hnd o
    unfold hasRoleIn at hnd
    rw [List.any_eq_false] at hnd
    have := hnd (o, l) hmem
    simpa using this
  rintro ⟨q, hg, hpq⟩
  -- grant u r = some q. Show q = .read, contradicting hpne via hpq.
  have hqr : q = .read := by
    -- Case split on sensitivity first
    by_cases hs : isSensitiveData r = true
    · unfold grant at hg
      rw [if_pos (by simp [hs])] at hg
      unfold grantSensitive at hg
      split at hg
      · rename_i hall
        obtain ⟨_, hmgr⟩ := hall
        rw [hnm r.ownerOrg] at hmgr
        exact absurd hmgr (by decide)
      · contradiction
    · have hns : isSensitiveData r = false := by
        cases h : isSensitiveData r
        · rfl
        · exact absurd h hs
      unfold grant at hg
      rw [if_neg (by simp [hns])] at hg
      unfold grantOpen at hg
      -- All four parts give at most .read for a pure developer
      rcases Option.mergePerm_eq_some_or hg with h1 | hcross
      · rcases Option.mergePerm_eq_some_or h1 with h2 | hread
        · rcases Option.mergePerm_eq_some_or h2 with hdel | hedit
          · unfold sameDeletePart at hdel
            split at hdel
            · rename_i hall
              obtain ⟨_, hcond⟩ := hall
              rcases hcond with ⟨hdev, _⟩ | ⟨hmgr, _⟩
              · rw [hnd r.ownerOrg] at hdev; exact absurd hdev (by decide)
              · rw [hnm r.ownerOrg] at hmgr; exact absurd hmgr (by decide)
            · contradiction
          · unfold sameEditPart at hedit
            split at hedit
            · rename_i hall
              obtain ⟨_, hcond⟩ := hall
              rcases hcond with ⟨hmgr, _⟩ | ⟨hdev, _⟩
              · rw [hnm r.ownerOrg] at hmgr; exact absurd hmgr (by decide)
              · rw [hnd r.ownerOrg] at hdev; exact absurd hdev (by decide)
            · contradiction
        · rcases sameReadPart_eq u r with h | h <;> rw [h] at hread
          · cases hread; rfl
          · contradiction
      · unfold crossReadPart at hcross
        split at hcross
        · rename_i hall
          obtain ⟨_, hcond⟩ := hall
          rcases hcond with hmgr | ⟨_, hdev⟩ | ⟨_, hdvo⟩
          · rw [hnam] at hmgr; exact absurd hmgr (by decide)
          · -- developer anywhere – actually allowed for rule 6 (data cross-org).
            -- Pure developer *does* have read on data cross-org.
            cases hcross; rfl
          · rw [hnad] at hdvo; exact absurd hdvo (by decide)
        · contradiction
  subst hqr
  -- hpq : p ≤ .read, hpne : p ≠ .read
  have : p = .read := Permission.le_antisymm hpq (Permission.read_le p)
  exact hpne this

/-! ## Tier 1.6 — Cross-org denial -/

/-- Cross-org means no edit and no delete. -/
theorem not_Can_edit_otherOrg (u : User) (r : Resource)
    (hother : otherOrg u r = true) : ¬ Can u r .edit := by
  rintro ⟨q, hg, hpq⟩
  by_cases hs : isSensitiveData r = true
  · unfold grant at hg
    rw [if_pos (by simp [hs])] at hg
    unfold grantSensitive at hg
    split at hg
    · rename_i hall
      obtain ⟨hso, _⟩ := hall
      have := not_sameOrg_of_otherOrg hother
      rw [this] at hso; exact Bool.false_ne_true hso
    · contradiction
  · have hns : isSensitiveData r = false := by
      cases h : isSensitiveData r
      · rfl
      · exact absurd h hs
    unfold grant at hg
    rw [if_neg (by simp [hns])] at hg
    unfold grantOpen at hg
    have hso_false : sameOrg u r = false := not_sameOrg_of_otherOrg hother
    -- All same-org parts are none; only crossRead (at most .read) fires.
    -- So q ≤ .read, contradicting .edit ≤ q.
    rcases Option.mergePerm_eq_some_or hg with h1 | hcross
    · rcases Option.mergePerm_eq_some_or h1 with h2 | hread
      · rcases Option.mergePerm_eq_some_or h2 with hdel | hedit
        · unfold sameDeletePart at hdel
          split at hdel
          · rename_i hall
            exact absurd (hall.1) (by rw [hso_false]; decide)
          · contradiction
        · unfold sameEditPart at hedit
          split at hedit
          · rename_i hall
            exact absurd (hall.1) (by rw [hso_false]; decide)
          · contradiction
      · unfold sameReadPart at hread
        split at hread
        · rename_i hso; rw [hso_false] at hso; exact Bool.false_ne_true hso
        · contradiction
    · rcases crossReadPart_eq u r with h | h <;> rw [h] at hcross
      · cases hcross
        -- hpq : .edit ≤ .read is false
        exact absurd hpq (by decide)
      · contradiction

/-- Cross-org means no delete. -/
theorem not_Can_delete_otherOrg (u : User) (r : Resource)
    (hother : otherOrg u r = true) : ¬ Can u r .delete := fun h =>
  not_Can_edit_otherOrg u r hother (Can.delete_to_edit h)

/-! ## Tier 1.7 — Closed-world witness -/

/-- Already in `Access`: `grant u r = none → ¬ Can u r p`. -/
theorem closed_world (u : User) (r : Resource) :
    grant u r = none → ∀ p, ¬ Can u r p :=
  fun h p => Can.of_grant_none h p

/-! ## Tier 1.8 — Rule subsumption -/

/-- Rule 8 strictly subsumes rule 3 (via grant-closure): if a user can delete a
non-data same-org resource, they can also edit it. -/
theorem rule3_of_rule8 (u : User) (r : Resource) (hso : sameOrg u r = true)
    (hdev : hasRoleIn u r.ownerOrg .devops = true) (hrt : r.resourcetype ≠ .data) :
    Can u r .edit :=
  Can.delete_to_edit (Derivable.rule8 hso hdev hrt).sound

/-- Rule 9 strictly subsumes rule 2: manager + data + same-org can edit. -/
theorem rule2_of_rule9 (u : User) (r : Resource) (hso : sameOrg u r = true)
    (hmgr : hasRoleIn u r.ownerOrg .manager = true) (hdata : r.resourcetype = .data) :
    Can u r .edit :=
  Can.delete_to_edit (Derivable.rule9 hso hmgr hdata).sound

/-! ## Tier 2 — per-rule sanity -/

/-- Rule 1 stated positively on `Can`. -/
theorem Can_read_of_sameOrg_nonSensitive (u : User) (r : Resource)
    (hso : sameOrg u r = true) (hns : isSensitiveData r = false) : Can u r .read :=
  (Derivable.rule1 hso hns).sound

/-- Rule 2 (as a Can-level fact; note: holds even when sensitive by rule 10 + closure). -/
theorem Can_edit_of_manager_data (u : User) (r : Resource)
    (hso : sameOrg u r = true) (hmgr : hasRoleIn u r.ownerOrg .manager = true)
    (hdata : r.resourcetype = .data) : Can u r .edit :=
  (Derivable.rule2 hso hmgr hdata).sound

/-- Rule 3. -/
theorem Can_edit_of_devops_nonData (u : User) (r : Resource)
    (hso : sameOrg u r = true) (hdev : hasRoleIn u r.ownerOrg .devops = true)
    (hrt : r.resourcetype ≠ .data) : Can u r .edit :=
  (Derivable.rule3 hso hdev hrt).sound

/-- Rule 8. -/
theorem Can_delete_of_devops_nonData (u : User) (r : Resource)
    (hso : sameOrg u r = true) (hdev : hasRoleIn u r.ownerOrg .devops = true)
    (hrt : r.resourcetype ≠ .data) : Can u r .delete :=
  (Derivable.rule8 hso hdev hrt).sound

/-- Rule 9. -/
theorem Can_delete_of_manager_data (u : User) (r : Resource)
    (hso : sameOrg u r = true) (hmgr : hasRoleIn u r.ownerOrg .manager = true)
    (hdata : r.resourcetype = .data) : Can u r .delete :=
  (Derivable.rule9 hso hmgr hdata).sound

/-- Rule 10. -/
theorem Can_delete_of_sensitive_manager (u : User) (r : Resource)
    (hs : isSensitiveData r = true) (hso : sameOrg u r = true)
    (hmgr : hasRoleIn u r.ownerOrg .manager = true) : Can u r .delete :=
  (Derivable.rule10 hs hso hmgr).sound

/-! ## Tier 3 — frame and monotonicity -/

/-- Frame: `Can` is a function of `(u, r, p)` alone. Adding unrelated world state
cannot change it. Stated here as a tautology to pin the property. -/
theorem Can_frame (u : User) (r : Resource) (p : Permission) :
    Can u r p ↔ Can u r p := Iff.rfl

/-- If `u.memberships ⊆ u'.memberships`, `u'` has at least the same powers as `u`. -/
theorem sameOrg_mono {u u' : User} {r : Resource}
    (hsub : ∀ m, m ∈ u.memberships → m ∈ u'.memberships)
    (h : sameOrg u r = true) : sameOrg u' r = true := by
  unfold sameOrg at *
  rw [List.any_eq_true] at *
  obtain ⟨m, hm, hcond⟩ := h
  exact ⟨m, hsub m hm, hcond⟩

/-- Monotonicity check for role-membership lookup: superset memberships preserve
`hasRoleIn` truth. -/
theorem hasRoleIn_mono {u u' : User} {o : OrgId} {l : Level}
    (hsub : ∀ m, m ∈ u.memberships → m ∈ u'.memberships)
    (h : hasRoleIn u o l = true) : hasRoleIn u' o l = true := by
  unfold hasRoleIn at *
  rw [List.any_eq_true] at *
  obtain ⟨m, hm, hcond⟩ := h
  exact ⟨m, hsub m hm, hcond⟩

/-- Monotonicity check for global role lookup: superset memberships preserve
`hasRoleAnywhere` truth. -/
theorem hasRoleAnywhere_mono {u u' : User} {l : Level}
    (hsub : ∀ m, m ∈ u.memberships → m ∈ u'.memberships)
    (h : hasRoleAnywhere u l = true) : hasRoleAnywhere u' l = true := by
  unfold hasRoleAnywhere at *
  rw [List.any_eq_true] at *
  obtain ⟨m, hm, hcond⟩ := h
  exact ⟨m, hsub m hm, hcond⟩

/-- Membership-monotonicity: adding memberships only increases access. -/
theorem Can_membership_mono {u u' : User} {r : Resource} {p : Permission}
    (hsub : ∀ m, m ∈ u.memberships → m ∈ u'.memberships) :
    Can u r p → Can u' r p := by
  intro h
  rw [Can_iff_Derivable] at *
  induction h with
  | rule1 hso hns => exact .rule1 (sameOrg_mono hsub hso) hns
  | rule2 hso hmgr hdata => exact .rule2 (sameOrg_mono hsub hso) (hasRoleIn_mono hsub hmgr) hdata
  | rule3 hso hdev hrt => exact .rule3 (sameOrg_mono hsub hso) (hasRoleIn_mono hsub hdev) hrt
  | weaken hpq _ ih => exact .weaken hpq ih
  | rule5 hmgr hns => exact .rule5 (hasRoleAnywhere_mono hsub hmgr) hns
  | rule6 hother hdev hdata hns =>
    by_cases hso' : sameOrg u' r = true
    · exact .rule1 hso' hns
    · have : otherOrg u' r = true := otherOrg_of_not_sameOrg (by
        cases h : sameOrg u' r
        · rfl
        · exact absurd h hso')
      exact .rule6 this (hasRoleAnywhere_mono hsub hdev) hdata hns
  | rule7 hother hdev hrt =>
    by_cases hso' : sameOrg u' r = true
    · -- u' is sameOrg now; use rule1 on non-sensitive (ensured since hrt ≠ data)
      have hns : isSensitiveData r = false := isSensitiveData_of_not_data r hrt
      exact .rule1 hso' hns
    · have : otherOrg u' r = true := otherOrg_of_not_sameOrg (by
        cases h : sameOrg u' r
        · rfl
        · exact absurd h hso')
      exact .rule7 this (hasRoleAnywhere_mono hsub hdev) hrt
  | rule8 hso hdev hrt => exact .rule8 (sameOrg_mono hsub hso) (hasRoleIn_mono hsub hdev) hrt
  | rule9 hso hmgr hdata => exact .rule9 (sameOrg_mono hsub hso) (hasRoleIn_mono hsub hmgr) hdata
  | rule10 hs hso hmgr =>
    exact .rule10 hs (sameOrg_mono hsub hso) (hasRoleIn_mono hsub hmgr)

/-- Role-addition monotonicity: adding a new (org, role) to memberships keeps all
existing access and may grant more. -/
theorem Can_role_addition_mono (u : User) (r : Resource) (p : Permission)
    (o : OrgId) (l : Level) :
    Can u r p → Can { u with memberships := (o, l) :: u.memberships } r p := by
  apply Can_membership_mono
  intro m hm
  exact List.mem_cons_of_mem _ hm

/-- **Resource sensitivity is anti-monotone** — the *only* non-monotone axis in
the model. Flipping `sensitivity` from `true` to `false` can only widen access. -/
theorem Can_sensitivity_antimono (u : User) (r : Resource) (p : Permission)
    (hdata : r.resourcetype = .data) :
    Can u { r with sensitivity := true } p → Can u { r with sensitivity := false } p := by
  intro h
  have hs : isSensitiveData { r with sensitivity := true } = true := by
    unfold isSensitiveData; rw [hdata]
  rw [Can_of_sensitive _ _ p hs] at h
  obtain ⟨hso, hmgr⟩ := h
  -- same-org manager → can delete the non-sensitive data version
  have hso' : sameOrg u { r with sensitivity := false } = true := by
    unfold sameOrg at *; exact hso
  have hmgr' : hasRoleIn u ({r with sensitivity := false}).ownerOrg .manager = true := by
    unfold hasRoleIn at *; exact hmgr
  have hdata' : ({r with sensitivity := false}).resourcetype = .data := hdata
  exact Can.weaken (Permission.le_delete p)
    ((Derivable.rule9 hso' hmgr' hdata').sound)

/-- The converse of anti-monotonicity fails: flipping sensitivity false → true
strictly *removes* access for non-managers. Concretely: a same-org developer
reading non-sensitive data loses that access when the data becomes sensitive. -/
theorem sensitivity_true_blocks_non_manager
    (u : User) (r : Resource)
    (hdata : r.resourcetype = .data)
    (_hso : sameOrg u r = true)
    (hnmgr : hasRoleIn u r.ownerOrg .manager = false) :
    ¬ Can u { r with sensitivity := true } .read := by
  have hs : isSensitiveData { r with sensitivity := true } = true := by
    unfold isSensitiveData; rw [hdata]
  have hnmgr' : hasRoleIn u ({r with sensitivity := true}).ownerOrg .manager = false := hnmgr
  exact not_Can_sensitive_sameOrg_nonManager u _ hs hnmgr' .read

/-! ## Tier 4 — sanity: idempotence of memberships order -/

/-- `sameOrg` is invariant under any permutation of memberships. -/
theorem sameOrg_perm {u u' : User} {r : Resource}
    (hperm : ∀ m, m ∈ u.memberships ↔ m ∈ u'.memberships) :
    sameOrg u r = sameOrg u' r := by
  unfold sameOrg
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  exact ⟨fun ⟨m, hm, hc⟩ => ⟨m, (hperm m).mp hm, hc⟩,
         fun ⟨m, hm, hc⟩ => ⟨m, (hperm m).mpr hm, hc⟩⟩

/-- `hasRoleIn` is invariant under any permutation of memberships. -/
theorem hasRoleIn_perm {u u' : User} {o : OrgId} {l : Level}
    (hperm : ∀ m, m ∈ u.memberships ↔ m ∈ u'.memberships) :
    hasRoleIn u o l = hasRoleIn u' o l := by
  unfold hasRoleIn
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  exact ⟨fun ⟨m, hm, hc⟩ => ⟨m, (hperm m).mp hm, hc⟩,
         fun ⟨m, hm, hc⟩ => ⟨m, (hperm m).mpr hm, hc⟩⟩

end LeanACL
