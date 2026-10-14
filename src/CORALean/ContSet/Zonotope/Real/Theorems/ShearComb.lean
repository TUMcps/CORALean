module

public import CORALean.ContSet.Zonotope.Real.Operations.Shear
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The sheared combination is the shear of the combination

`(c' + ∑ βⱼ g'ⱼ) = S (c + ∑ βⱼ gⱼ)` for the sheared centre and generators: the shear is linear,
which carries a section of the zonogon of [1, Alg. 3] to a vertical one.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.shear_comb (Z : Zonotope (Vec ℝ 2)) (κ : ℝ) (β : Fin Z.h → ℝ) :
    (Z.shear κ).c + ∑ j, β j • (Z.shear κ).G j
      = ![(Z.c + ∑ j, β j • Z.G j) 0 - κ * (Z.c + ∑ j, β j • Z.G j) 1,
          (Z.c + ∑ j, β j • Z.G j) 1] := by -- --- PROOF ---
  have e0 := Zonotope.comb_apply Z β 0
  have e1 := Zonotope.comb_apply Z β 1
  ext k
  fin_cases k
  · simp only [Zonotope.shear, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fin.zero_eta, Matrix.cons_val_zero, e0, e1, mul_sub, Finset.sum_sub_distrib]
    have : ∑ x, β x * (κ * Z.G x 1) = κ * ∑ x, β x * Z.G x 1 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [this]; ring
  · simp [Zonotope.shear, Finset.sum_apply, e1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
