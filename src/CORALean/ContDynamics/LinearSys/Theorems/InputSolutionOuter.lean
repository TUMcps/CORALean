module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuterOfRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.RemainderEntryLe
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ContinuousExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.InputRemainderSet

@[expose] public section

/-!
# `inputSolution` contains everything the input can contribute over a step

Althoff's Thm. 3.1. Substituting `τ = r - s` turns `∫₀ʳ e^{A(r-s)}u(s)ds` into `∫₀ʳ e^{Aτ}u(r-τ)dτ`,
and the exponential splits into its first `η+1` orders plus a remainder, a *finite* sum, so
linearity of the integral does the whole split. Each exact order comes out as `Aⁱ/i!` applied to
`∫₀ʳ τⁱ u(r-τ)dτ`, the matrix leaving the integral before `integral_pow_smul_mem` is used, so
convexity is asked only of `U`. The remainder cannot do that, `R(τ)` varying with `τ`, so there the
convex closed set is the product `E(r)·r·U`. `0 ∈ U` is not needed: this is the enclosure at `r`,
and Prop. 3.3 would extend it to all of `[0,r]`.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
theorem LinearSys.inputSolution_outer [Mtimes ℐ S]
    (sys : LinearSys 𝕋 n)
    {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (hconv : Convex ℝ (toSet U)) (hclosed : IsClosed (toSet U))
    (hbdd : Bornology.IsBounded (toSet U))
    -- the next three are asked of the product and not of `U`, `R(τ)` varying with `τ`
    (hRconv : Convex ℝ (MatExp.inputRemainderSet (toRealMat sys.A) r η U))
    (hRclosed : IsClosed (MatExp.inputRemainderSet (toRealMat sys.A) r η U))
    (hRbdd : Bornology.IsBounded (MatExp.inputRemainderSet (toRealMat sys.A) r η U))
    {u : ℝ → Vec ℝ n}
    (hu : ∀ τ ∈ Set.Ioc (0:ℝ) r, u (r - τ) ∈ toSet U)
    (hmeas : AEStronglyMeasurable (fun τ => u (r - τ)) (volume.restrict (Set.Ioc 0 r)))
    : -- --- CONCL ---
    (∫ s in (0:ℝ)..r, exp ((r - s) • toRealMat sys.A) *ᵥ u s)
      ∈ toSet (sys.inputSolution r η U) := by -- --- PROOF ---
  -- every scaled remainder is in `inputRemainder`, entry by entry
  refine sys.inputSolution_outer_of_remainder hr η (MatExp.inputRemainder (toRealMat sys.A) r η)
    ?_ hconv hclosed hbdd hRconv hRclosed hRbdd hu hmeas
  intro τ hτ
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have hb := MatExp.remainder_entry_le (toRealMat sys.A) η hr hτ.1.le hτ.2 hε j k
  rw [abs_le] at hb
  refine ⟨?_, ?_⟩
  · show -(r * _) ≤ r * _
    nlinarith [hb.1, hr.le]
  · show r * _ ≤ r * _
    nlinarith [hb.2, hr.le]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
