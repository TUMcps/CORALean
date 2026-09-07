import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
import CORALean.Global.LinProg.API

/-!
# A box answers a direction corner by corner

No linear program: a linear functional on `Vec ℝ n` expands over the standard
basis, so its value at `x` is `∑ i, x i * c (Pi.single i 1)`, and each summand
is between the two corner products by `Interval.mul_between_endpoints`. Needs
coordinates, so this is at `Vec ℝ n` and not a general `Entrywise` ambient type
— `Interval (Mat ℝ m n)` gets none from this.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No linear program: the value is a sum of corner products, one per
coordinate, each attained by moving that coordinate to its far endpoint. -/
noncomputable def Interval.supportBound (I : Interval (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound I.construct c where
  val := ∑ i, max (c (Pi.single i 1) * I.inf i) (c (Pi.single i 1) * I.sup i)
  le := by
    intro x hx
    have hc : c x = ∑ i, x i * c (Pi.single i 1) := by
      conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ c x]
      refine Finset.sum_congr rfl fun i _ => ?_
      have heq : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i (1 : ℝ) := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [heq, smul_eq_mul]
    rw [hc]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]
    exact (Interval.mul_between_endpoints (hx i).1 (hx i).2).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
