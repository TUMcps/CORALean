import CORALean.ContDynamics.LinearSys.Operations.ConstInputSolution
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint

/-!
# `constInputSolution` holds what the constant contributes, at every time of the step

At `t ∈ [0, r]`, `∫₀ᵗ e^{Aσ}dσ ũ` is the straight line `∫₀ʳ e^{Aσ}dσ ((t/r) ũ)`
plus `(∫₀ᵗ e^{Aσ}dσ - (t/r) ∫₀ʳ e^{Aσ}dσ) ũ`: the first factor applied to a
point of the segment `[0, ũ]`, the second a member of `F̃` [1, Prop. 3.4]
applied to `ũ` itself. `plus_outer` adds them.

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
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the constant `ũ` contributes by any `t ∈ [0, r]` lies in
`constInputSolution r η ũ`, at an order admissible for `r`. -/
theorem LinearSys.expIntegral_mem_constInputSolution (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r)
    (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (uc : Vec ℝ n) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    MatExp.expIntegral (toRealMat sys.A) t *ᵥ uc
      ∈ construct (sys.constInputSolution (S := S) r η uc) := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  -- the straight line to the value at `r`, plus the interpolation error
  have hdecomp : MatExp.expIntegral A t *ᵥ uc
      = (MatExp.expIntegral A r *ᵥ ((t / r) • uc))
        + (MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r) *ᵥ uc := by
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec]
    abel
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the line: `∫₀ʳ e^{Aσ}dσ` at the point `(t/r) ũ` of the segment `[0, ũ]`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl
      (Set.mem_image_of_mem _ (smul_mem_linComb_ofPoint uc ⟨hs0, hs1⟩)))
  · -- the error: a member of `F̃`, at `ũ`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expIntegralDiff_mem_constCorrectionMatrix A hr η hε ht0 htr)
      (Set.mem_image_of_mem _ (OfPoint.mem_ofPoint uc)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
