module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrSumsFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# `MatExp.verifyCorrSumsFloat` brackets the sums of the clamped terms

If every term's box holds a number `xᵢ`, the lower sum is below `Σ min(xᵢ, 0)` and the upper sum
above `Σ max(xᵢ, 0)`: by induction over the terms, each addition rounded in its direction and the
clamping at `0` monotone.

## Inputs
* `T` – float term boxes by index
* `x` – the real numbers they hold
* `j` – row index
* `k` – column index
* `m` – number of terms

## Hypotheses
* `hT` – each term's box holds its number at the entry

## Conclusion
* the two sums bracket the sums of the clamped numbers
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.verifyCorrSumsFloat_bracket (T : ℕ → Interval (Mat 𝕋 n n)) (x : ℕ → ℝ)
    (j k : Fin n) (hT : ∀ i, toReal ((T i).inf j k) ≤ x i ∧ x i ≤ toReal ((T i).sup j k))
    (m : ℕ) : -- --- CONCL ---
    toReal ((MatExp.verifyCorrSumsFloat ((List.range m).map T)).inf j k)
        ≤ ∑ i ∈ Finset.range m, min (x i) 0
      ∧ ∑ i ∈ Finset.range m, max (x i) 0
        ≤ toReal
          ((MatExp.verifyCorrSumsFloat ((List.range m).map T)).sup j k) := by -- --- PROOF ---
  simp only [MatExp.verifyCorrSumsFloat, Interval.materialiseMat_eq, List.foldl_map]
  induction m with
  | zero => simp [toReal_zero]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, Finset.sum_range_succ, Finset.sum_range_succ]
    refine ⟨le_trans (addDown_le_add _ _) (add_le_add ih1 ?_),
      le_trans (add_le_add ih2 ?_) (add_le_addUp _ _)⟩
    · rw [toReal_minimum, toReal_zero]; exact min_le_min_right _ (hT m).1
    · rw [toReal_maximum, toReal_zero]; exact max_le_max_right _ (hT m).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
