module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A linear functional on states is the sum of its rows

A linear functional on `Fin n → ℝ` is `Σⱼ f(e_j) xⱼ`: the coefficient of `x(j)` in a row of a
polytope is the functional at the unit vector.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped BigOperators

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.linearMap_apply_eq_sum (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = ∑ j, f (Pi.single j 1) * x j := by -- --- PROOF ---
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ f x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  funext k
  simp [Pi.single_apply, eq_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
