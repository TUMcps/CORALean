module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `‖G u‖₂² = uᵀ Gᵀ G u`

The squared length of a combination of the generators is the Gram quadratic form of the
coefficients, the identity behind [1, Def. 3]'s `uᵀ Gᵀ G u`.

## Inputs
* `Z` – zonotope
* `β` – generator coefficients

## Hypotheses
* none

## Conclusion
* the squared norm of the sum is a Gram form of the coefficients

## References

* [1] [V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". 2020 American Control Conference (ACC),
      2020.](../../../../../../references/2020/gassmann-acc-zonotope-ellipsoid.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sq_norm₂_sum_eq_gram (Z : Zonotope (Vec ℝ n)) (β : Fin Z.h → ℝ) : -- --- CONCL ---
    ‖∑ j, β j • Z.G j‖₂ ^ 2 =
      β ⬝ᵥ ((Matrix.of fun j k => Z.G j ⬝ᵥ Z.G k) *ᵥ β) := by -- --- PROOF ---
  rw [← dotProduct_self, sum_dotProduct]
  simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
