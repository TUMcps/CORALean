module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint

@[expose] public section

/-!
# `constInputSolution` holds what the constant contributes, at every member

`LinearSys.expIntegral_mem_constInputSolution` at an interval matrix, feeding
[1, Alg. 4]'s split case: at `t ∈ [0, r]`, `∫₀ᵗ e^{Aσ}dσ ũ` is the straight
line `C(r)((t/r) ũ)` plus a member of [1, Prop. 3.4]'s `F̃` applied to `ũ`, the
first through `inputSolution_outer` at the constant input `(t/r) ũ` on the
segment `[0, ũ]`, the second through
`expIntegralDiff_mem_intervalConstCorrectionMatrix`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, ConvexSet (S n) (Vec ℝ n)]
variable [∀ n, CompactSet (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the constant `ũ` contributes by any `t ∈ [0, r]`, at any member `A` of
`sys.A`, lies in `constInputSolution r η ũ`, at an order admissible for `r`. -/
theorem LinParamSys.expIntegral_mem_constInputSolution (sys : LinParamSys ℐ n)
    {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) (uc : Vec ℝ n) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    MatExp.expIntegral A t *ᵥ uc
      ∈ construct (sys.constInputSolution (S := S) r η uc) := by -- --- PROOF ---
  set seg : S n := LinComb.linComb (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint uc) with hseg
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
  · -- `C(r)` applied to the segment is a constant input's own `inputSolution`
    have hline := sys.inputSolution_outer hr η hε hA (ConvexSet.convex_construct seg)
      (CompactSet.isClosed_construct seg) (CompactSet.isBounded_construct seg)
      (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
      (CompactSet.isBounded_construct _) (u := fun _ : ℝ => (t / r) • uc)
      (fun _ _ => smul_mem_linComb_ofPoint uc ⟨hs0, hs1⟩) aestronglyMeasurable_const
    rwa [Real.MatExp.expIntegral_constInput A ((t / r) • uc) hr.le] at hline
  · -- the error: a member of `F̃`, at `ũ`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix sys.A hr η hε hA ht0 htr)
      (Set.mem_image_of_mem _ (OfPoint.mem_ofPoint uc)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
