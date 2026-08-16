import CORALean.Global.Mathlib

/-!
# Splitting an index type into parts

`Split α into β` names every index of `α` exactly once as `P.on k l`, where
`k` picks a part and `l` an index within it. Two parts are the common case and
read `Split α into βₗ and βᵣ`, with `P.left` and `P.right`.

`sum_split` is why the type exists — a sum over `α` splits along the parts with
no side condition, since the equivalence already rules out overlap.

The type is `Partition`; `Split` is only its notation. Naming the two alike
would make `Partition` a keyword, and `Partition.left` would print quoted.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

universe v

structure Partition (α : Type*) {κ : Type*} (β : κ → Type*) where
  index : (Σ k, β k) ≃ α

/-- The two-part family. -/
def Pair (β γ : Type v) : Bool → Type v
  | true => β
  | false => γ

/-- Two parts, the common case. Its own name is what makes it print as one. -/
abbrev Partition₂ (α : Type*) (β γ : Type v) := Partition α (Pair β γ)

notation:50 "Split " α:max " into " β:max => CORALean.Partition α β
notation:50 "Split " α:max " into " β:max " and " γ:max => CORALean.Partition₂ α β γ

instance {β γ : Type v} [Fintype β] [Fintype γ] : (b : Bool) → Fintype (Pair β γ b)
  | true => inferInstanceAs (Fintype β)
  | false => inferInstanceAs (Fintype γ)

variable {α κ M : Type*} {β : κ → Type*} {βₗ βᵣ : Type v}

def Partition.on (P : Split α into β) (k : κ) (l : β k) : α := P.index ⟨k, l⟩

def Partition.left (P : Split α into βₗ and βᵣ) (l : βₗ) : α := P.on true l

def Partition.right (P : Split α into βₗ and βᵣ) (l : βᵣ) : α := P.on false l

theorem Partition.sum_split [AddCommMonoid M] [Fintype α] [Fintype κ] [∀ k, Fintype (β k)]
    (P : Split α into β) (f : α → M) :
    ∑ j, f j = ∑ k, ∑ l, f (P.on k l) := by
  rw [← Equiv.sum_comp P.index f, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

theorem Partition.sum_split₂ [AddCommMonoid M] [Fintype α] [Fintype βₗ] [Fintype βᵣ]
    (P : Split α into βₗ and βᵣ) (f : α → M) :
    ∑ j, f j = ∑ l, f (P.left l) + ∑ l, f (P.right l) := by
  rw [P.sum_split f, Fintype.sum_bool]
  rfl

end CORALean
