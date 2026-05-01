/-!
# LeanACL.Terms

Core enumerations (`Level`, `Permission`, `ResourceType`) and records
(`Organization`, `Resource`, `User`).

The `Permission` chain `read ≤ edit ≤ delete` encodes rule 4 of the spec
(grant-closure): if the policy grants `q`, it also grants every `p ≤ q`.
We model this as a numeric rank so that `≤` is decidable and reuses `Nat`'s
order theory.

`Resource.sensitivity : Bool` carries the rule-10 override flag. It is only
*semantically* meaningful when `resourcetype = .data`; the theorem
`Can` is invariant under `sensitivity` for non-data resources (see
`LeanACL.Theorems`). We keep the field on every `Resource` rather than
inside the `data` constructor to stay faithful to the English spec.
-/

namespace LeanACL

/-- A user's role *within a given organization*. Roles are stored per-org on
`User.memberships`; there is no global level. -/
inductive Level where
  | manager
  | developer
  | devops
  deriving Repr, DecidableEq, BEq

/-- The access levels a policy can grant. Ordered as
`read ≤ edit ≤ delete` via `Permission.rank`. -/
inductive Permission where
  | read
  | edit
  | delete
  deriving Repr, DecidableEq, BEq

/-- Category of a resource. `sensitivity` only has effect on `data`. -/
inductive ResourceType where
  | storage
  | compute
  | data
  deriving Repr, DecidableEq, BEq

/-- Numeric rank witnessing the total order on `Permission`. -/
def Permission.rank : Permission → Nat
  | .read => 0
  | .edit => 1
  | .delete => 2

instance : LE Permission where
  le a b := a.rank ≤ b.rank

instance : LT Permission where
  lt a b := a.rank < b.rank

instance (a b : Permission) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.rank ≤ b.rank))

instance (a b : Permission) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.rank < b.rank))

namespace Permission

/-- Reflexivity check for the permission preorder (`p ≤ p`). -/
theorem le_refl (a : Permission) : a ≤ a := Nat.le_refl _

/-- Transitivity check for permission ordering (`a ≤ b ≤ c → a ≤ c`). -/
theorem le_trans {a b c : Permission} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

/-- Antisymmetry check for permission ordering (`a ≤ b` and `b ≤ a` implies equality). -/
theorem le_antisymm : ∀ {a b : Permission}, a ≤ b → b ≤ a → a = b := by
  intro a b hab hba
  have : a.rank = b.rank := Nat.le_antisymm hab hba
  cases a <;> cases b <;> simp_all [rank]

/-- Totality check: any two permissions are comparable. -/
theorem le_total (a b : Permission) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.rank b.rank

/-- Bottom-element check: `read` is below every permission. -/
theorem read_le (p : Permission) : Permission.read ≤ p := by
  cases p <;> decide

/-- Top-element check: every permission is below `delete`. -/
theorem le_delete (p : Permission) : p ≤ Permission.delete := by
  cases p <;> decide

/-- Chain edge check: `read ≤ edit`. -/
theorem read_le_edit : Permission.read ≤ Permission.edit := by decide

/-- Chain edge check: `edit ≤ delete`. -/
theorem edit_le_delete : Permission.edit ≤ Permission.delete := by decide

/-- Derived chain check: `read ≤ delete`. -/
theorem read_le_delete : Permission.read ≤ Permission.delete := by decide

/-- The lattice join on `Permission`: the stronger of two permissions. -/
def max (a b : Permission) : Permission :=
  if a ≤ b then b else a

/-- Join upper-bound check for the left argument (`a ≤ max a b`). -/
theorem le_max_left (a b : Permission) : a ≤ max a b := by
  unfold max
  split
  · assumption
  · exact le_refl a

/-- Join upper-bound check for the right argument (`b ≤ max a b`). -/
theorem le_max_right (a b : Permission) : b ≤ max a b := by
  unfold max
  split
  · exact le_refl b
  · rename_i h
    rcases le_total a b with hab | hab
    · exact absurd hab h
    · exact hab

/-- Least-upper-bound check: if both inputs are below `c`, so is `max a b`. -/
theorem max_le {a b c : Permission} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  unfold max
  split
  · exact hb
  · exact ha

end Permission

/-- Identifier for an `Organization`. Kept abstract (`Nat`) so proofs don't
depend on a particular registry. -/
abbrev OrgId := Nat

/-- An organization in the world model. Only `id` is used by the policy;
`name` is informational. -/
structure Organization where
  id   : OrgId
  name : String
  deriving Repr

/-- A resource to protect.

* `ownerOrg` — the organization that owns `r` (renamed from `parentOrg`;
  we do not model a containment hierarchy).
* `resourcetype` — `storage` / `compute` / `data`.
* `sensitivity` — rule 10 override; only meaningful when
  `resourcetype = .data`.
-/
structure Resource where
  ownerOrg     : OrgId
  resourcetype : ResourceType
  sensitivity  : Bool
  deriving Repr

/-- A user, with per-org role memberships.

The English spec put a single `level` on `User`; that forces the role to be
the same in every org the user belongs to. We generalise to a list of
`(OrgId × Level)` pairs so a user can be, say, a manager in one org and a
developer in another. -/
structure User where
  id          : Nat
  memberships : List (OrgId × Level)
  deriving Repr

end LeanACL
