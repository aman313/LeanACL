import LeanACL.Theorems
import Mathlib.Tactic

/-!
# LeanACL.Grind

Alternative proofs using `grind` for theorem shapes where automated
first-order reasoning works well (equalities, order facts, contradiction
closure, and straightforward rewriting).

These are intentionally additive: they do not replace the explicit proofs in
`Terms`, `Access`, and `Theorems`.
-/

namespace LeanACL

/-! ## Permission-chain lemmas (`grind` versions) -/

theorem Permission.read_le_edit_grind : Permission.read ≤ Permission.edit := by
  change (0 : Nat) ≤ 1
  grind

theorem Permission.edit_le_delete_grind : Permission.edit ≤ Permission.delete := by
  change (1 : Nat) ≤ 2
  grind

theorem Permission.read_le_delete_grind : Permission.read ≤ Permission.delete := by
  change (0 : Nat) ≤ 2
  grind

/-! ## Predicate-duality lemmas (`grind` versions) -/

theorem otherOrg_true_iff_sameOrg_false_grind (u : User) (r : Resource) :
    otherOrg u r = true ↔ sameOrg u r = false := by
  unfold otherOrg
  cases h : sameOrg u r <;> grind

theorem not_sameOrg_of_otherOrg_grind {u : User} {r : Resource}
    (h : otherOrg u r = true) : sameOrg u r = false := by
  grind [otherOrg_true_iff_sameOrg_false]

/-! ## Closed-world and weakening helpers (`grind` versions) -/

theorem Can.delete_to_edit_grind {u r} (h : Can u r .delete) : Can u r .edit := by
  exact Can.weaken Permission.edit_le_delete h

theorem Can.of_grant_none_grind {u r} (h : grant u r = none) (p : Permission) :
    ¬ Can u r p := by
  intro hcan
  obtain ⟨q, hq, _⟩ := hcan
  have : False := by grind
  exact False.elim this

/-! ## Security corollaries (`grind` versions) -/

theorem not_Can_sensitive_otherOrg_grind (u : User) (r : Resource)
    (hs : isSensitiveData r = true) (hother : otherOrg u r = true) :
    ¬ Can u r .read := by
  rw [Can_of_sensitive u r .read hs]
  intro hcan
  have hsofalse : sameOrg u r = false := not_sameOrg_of_otherOrg hother
  have : False := by grind
  exact False.elim this

theorem not_Can_delete_otherOrg_grind (u : User) (r : Resource)
    (hother : otherOrg u r = true) : ¬ Can u r .delete := by
  intro hdel
  have hedit : Can u r .edit := Can.delete_to_edit hdel
  exact not_Can_edit_otherOrg u r hother hedit

end LeanACL
