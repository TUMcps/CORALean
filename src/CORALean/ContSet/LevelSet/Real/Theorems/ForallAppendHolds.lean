module

public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Stacked constraints hold if each block holds

The stacked operator list and value vector of `and_` satisfy every comparison exactly when each
block does.

## Inputs
* `a` – number of rows of the first block
* `b` – number of rows of the second block
* `o₁` – operators of the first block
* `o₂` – operators of the second block
* `v₁` – values of the first block
* `v₂` – values of the second block

## Hypotheses
* none

## Conclusion
* all stacked rows hold iff each block holds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.forall_append_holds {a b : ℕ} (o₁ : Fin a → CompOp) (o₂ : Fin b → CompOp)
    (v₁ : Fin a → ℝ) (v₂ : Fin b → ℝ) :
    (∀ i, (Fin.append o₁ o₂ i).holds (Fin.append v₁ v₂ i)) ↔
      (∀ i, (o₁ i).holds (v₁ i)) ∧ ∀ j, (o₂ j).holds (v₂ j) := by
  rw [LevelSet.forall_fin_add]
  simp only [Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
