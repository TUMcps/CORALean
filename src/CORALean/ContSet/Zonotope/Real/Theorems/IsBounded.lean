module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# A zonotope is bounded

Coefficients run over `[-1,1]`, so a point reaches at most the center plus the
sum of the generator norms — the quantity `radius` computes at `Vec ℝ n`, here
only as a bound and never stored.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* `Z` is bounded
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   01-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isBounded_construct (Z : Zonotope α) : -- --- CONCL ---
    Bornology.IsBounded Z.construct := by -- --- PROOF ---
  refine isBounded_iff_forall_norm_le.mpr ⟨‖Z.c‖ + ∑ j, ‖Z.G j‖, ?_⟩
  rintro x ⟨β, hβ, rfl⟩
  have hgen : ‖∑ j, β j • Z.G j‖ ≤ ∑ j, ‖Z.G j‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hβ j)
  exact le_trans (norm_add_le _ _) (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
