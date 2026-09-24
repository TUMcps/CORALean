import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec

/-!
# `constPropagate` holds what a constant input contributes by `t_k`, at every member

[1, Alg. 4]'s split case, carried window by window: by induction on `k`,
`expIntegral A 0 = 0` starts it, and `expIntegral_add_mulVec` (`a := t_k`,
`b := Δt`) carries `t_k`'s value across one more window, `e^{AΔt}` a member of
`expEnclosure Δt η` and `Δt`'s own contribution a member of
`constInputSolution Δt η ũ` at its right end.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, ConvexSet (S n) (Vec ℝ n)]
variable [∀ n, CompactSet (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the constant `ũ` contributes by `t_k = k Δt`, at any member `A` of
`sys.A`, lies in `constPropagate Δt η ũ k`, at an order admissible for `Δt`. -/
theorem LinParamSys.expIntegral_mem_constPropagate (sys : LinParamSys ℐ n)
    {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) (uc : Vec ℝ n) : ∀ k : ℕ,
    MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ uc
      ∈ construct (sys.constPropagate (S := S) Δt η uc k)
  | 0 => by
    have hz : MatExp.expIntegral A (((0 : ℕ) : ℝ) * Δt) = 0 := by simp [MatExp.expIntegral]
    rw [hz, Matrix.zero_mulVec]
    exact OfPoint.mem_ofPoint 0
  | k + 1 => by
    have hrec := Real.MatExp.expIntegral_add_mulVec A uc (a := (k : ℝ) * Δt) (b := Δt)
      (by positivity) hΔt.le
    have htk : ((k + 1 : ℕ) : ℝ) * Δt = (k : ℝ) * Δt + Δt := by push_cast; ring
    rw [htk, hrec]
    exact Plus.plus_outer _ _ (Set.add_mem_add
      (Mtimes.mtimes_outer _ _ (Set.mem_biUnion (sys.exp_mem_expEnclosure Δt η hA)
        (Set.mem_image_of_mem _ (sys.expIntegral_mem_constPropagate hΔt η hε hA uc k))))
      (sys.expIntegral_mem_constInputSolution hΔt η hε hA uc hΔt.le (le_refl Δt)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
