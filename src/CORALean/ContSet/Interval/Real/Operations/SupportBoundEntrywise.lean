import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
import CORALean.Global.LinProg.API

/-!
# A box answers a direction corner by corner, over any coordinates

`Entrywise.eq_sum_single` writes a point as the sum of its coordinates, so a
linear functional's value is `∑ i, entry x i * c (ofEntry (Pi.single i 1))`,
and each summand is between the two corner products by
`Interval.mul_between_endpoints` — `Interval.supportBound`'s argument, carried
out over any `Entrywise` ambient type rather than `Vec ℝ n` alone. This gives
`Interval (Mat ℝ m n)` a support bound, which the `Vec`-only version could not.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- As `Interval.supportBound`, but over any `Entrywise` ambient type. -/
noncomputable def Interval.supportBoundEntrywise [Fintype ι] [DecidableEq ι]
    (I : Interval α) (c : α →ₗ[ℝ] ℝ) : SupportBound I.construct c where
  val := ∑ i, max (c (ofEntry (Pi.single i 1)) * entry I.inf i)
                  (c (ofEntry (Pi.single i 1)) * entry I.sup i)
  le := by
    intro x hx
    have hc : c x = ∑ i, entry x i * c (ofEntry (Pi.single i 1)) := by
      conv_lhs => rw [eq_sum_single x, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [hc]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]
    exact (Interval.mul_between_endpoints (hx i).1 (hx i).2).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
