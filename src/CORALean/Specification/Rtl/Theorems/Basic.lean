module

public import CORALean.Specification.Rtl.Definitions.Sat
public import CORALean.Specification.Rtl.Operations.Basic

@[expose] public section

/-!
# `Rtl/Theorems`: small theorems

One section per theorem, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {L X : Type}


-- =====================================  `Rtl.and?_spec`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)

/-- An empty operand gives the other, otherwise the conjunction. -/
theorem Rtl.and?_spec (o : Option (Rtl L)) (a b : Rtl L) :
    Rtl.and? none o = o ∧ Rtl.and? (some a) none = some a ∧
      Rtl.and? (some a) (some b) = some (.and a b) := ⟨rfl, rfl, rfl⟩


-- =================================  `Rtl.next?_eq_some_iff`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `next` succeeds exactly for the multiples of `0.5`, with the shifted formula. -/
theorem Rtl.next?_eq_some_iff (a ψ : Rtl L) (t : ℝ) :
    Rtl.next? a t = some ψ ↔ ψ = .next t a ∧ Rtl.IsHalfMultiple t := by
  unfold Rtl.next?
  by_cases h : Rtl.IsHalfMultiple t <;> simp [h, eq_comm]


-- ======================================  `Rtl.or?_spec`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An empty operand gives the other, otherwise the disjunction. -/
theorem Rtl.or?_spec (o : Option (Rtl L)) (a b : Rtl L) :
    Rtl.or? none o = o ∧ Rtl.or? (some a) none = some a ∧
      Rtl.or? (some a) (some b) = some (.or a b) := ⟨rfl, rfl, rfl⟩


-- ======================================  `Rtl.sat_all`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A leaf holds if it holds of every state of `R(0)`, Eq. (4). -/
theorem Rtl.sat_all (sat : L → X → Prop) (l : L) (R : ℝ≥0 → Set X) :
    (Rtl.all l).Sat sat R ↔ ∀ r ∈ R 0, sat l r := Iff.rfl


-- ======================================  `Rtl.sat_and`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A conjunction holds if both operands hold, Eq. (5). -/
theorem Rtl.sat_and (sat : L → X → Prop) (a b : Rtl L) (R : ℝ≥0 → Set X) :
    (Rtl.and a b).Sat sat R ↔ a.Sat sat R ∧ b.Sat sat R := Iff.rfl


-- ======================================  `Rtl.sat_next`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A `next` holds if the operand holds of the shifted reach sequence, Eq. (7). -/
theorem Rtl.sat_next (sat : L → X → Prop) (t : ℝ) (a : Rtl L) (R : ℝ≥0 → Set X) :
    (Rtl.next t a).Sat sat R ↔ a.Sat sat (Time.shift R t.toNNReal) := Iff.rfl


-- =======================================  `Rtl.sat_or`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A disjunction holds if one operand holds, Eq. (6). -/
theorem Rtl.sat_or (sat : L → X → Prop) (a b : Rtl L) (R : ℝ≥0 → Set X) :
    (Rtl.or a b).Sat sat R ↔ a.Sat sat R ∨ b.Sat sat R := Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
