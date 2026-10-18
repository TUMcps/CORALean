module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Operations.InputTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The preprint's (24) does not enclose the particular solution

[1, Prop. 1] approximates the particular solution `Z_S(Δt)` from outside by [1, (24)]. The first
preprint (arXiv v1) printed that formula, there (23), as
`⊕_{i=1}^{η} Aⁱ Δt^{i+1}/(i+1)! S ⊕ E(Δt, η) Δt S`, summing from `i = 1` and so dropping the
first order `Δt·S`; the later versions sum from `i = 0`. At `A = 0` the remainder `E` is the
zero matrix and every `Aⁱ` with `i ≥ 1` vanishes, so the printed set is `{0}`, while
`Z_S(Δt)` is `Δt·S`. `A = 0`, `Δt = 1`, `η = 0` and `S = [0, 2]` meet every side condition of the
proposition (`S` convex, closed, bounded, non-empty, and `Δt‖A‖ ≤ 1`), and `1 ∈ Z_S(1)`
is the constant input `u ≡ 1`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1] as arXiv v1 printed it: the particular solution lies in (24) summed from
`i = 1`. -/
theorem LinearSys.inputSolutionSet_printed_counterexample : -- --- STMT ---
    ¬ ∀ (n : ℕ) (sys : LinearSys ℝ n) (U : Zonotope (Vec ℝ n)) (Δt : ℝ), 0 < Δt → ∀ η : ℕ,
      sys.inputReach (S := 𝒵) U Δt
        ⊆ (∑ i ∈ Finset.Icc 1 η, (fun s => sys.inputTerm Δt i *ᵥ s) '' construct U)
          + ⋃ M ∈ (MatExp.inputRemainder (toRealMat sys.A) Δt η).construct,
              (fun s => M *ᵥ s) '' construct U := by -- --- PROOF ---
  intro h
  -- the constant input `1` reaches `1` over `[0, 1]` at `A = 0`
  have hmem : (fun _ => 1 : Vec ℝ 1) ∈
      (LinearSys.canonical 0 : LinearSys ℝ 1).inputReach (S := 𝒵)
        (⟨1, fun _ => 1, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 := by
    refine ⟨fun _ _ => 1, fun s _ => ⟨fun _ => 0, fun _ => by simp, by simp⟩, ?_, ?_⟩
    · exact aestronglyMeasurable_const
    · simp
  have := h 1 (LinearSys.canonical 0) ⟨1, fun _ => 1, fun _ _ => 1⟩ 1 one_pos 0 hmem
  simp at this
  obtain ⟨M, hM, x, _, hMx⟩ := this
  -- at `A = 0` the remainder is the zero matrix
  have hM0 := hM (0, 0)
  simp [MatExp.inputRemainder, MatExp.expRemainderBound] at hM0
  have hMz : M 0 0 = 0 := le_antisymm hM0.2 hM0.1
  have h1 := congrFun hMx 0
  simp [Matrix.mulVec, dotProduct, hMz] at h1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
