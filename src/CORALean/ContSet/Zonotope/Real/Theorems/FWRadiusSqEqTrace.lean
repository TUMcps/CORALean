import CORALean.ContSet.Zonotope.Real.Definitions.FWRadius
import CORALean.Global.TraceMulVecMulVecSelf
import Mathlib.Data.Matrix.Basic

/-!
# The squared F_W-radius is a trace

[1, Eq. 11]: `‖Ĥ‖²_{F,W} = tr(Ĥᵀ W Ĥ) = tr(W Ĥ Ĥᵀ) = tr(W P)`, `P = Ĥ Ĥᵀ = Σⱼ gⱼ gⱼᵀ`, for `W` with
`vᵀ W v ≥ 0`, which [1, Def. 4] has. Eq. 11 names the square `ℓ_{F,W+}` where Def. 4 names
the norm; it is the square that is a trace.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.fwRadius_sq_eq_trace (W : Mat ℝ n n) (hW : ∀ v, 0 ≤ v ⬝ᵥ (W *ᵥ v))
    (Z : Zonotope (Vec ℝ n)) :
    Z.fwRadius W ^ 2 = trace (W * ∑ j, vecMulVec (Z.G j) (Z.G j)) := by
  rw [Zonotope.fwRadius, Real.sq_sqrt (Finset.sum_nonneg fun j _ => hW _), Matrix.mul_sum,
    trace_sum]
  exact Finset.sum_congr rfl fun j _ => (trace_mul_vecMulVec_self W _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
