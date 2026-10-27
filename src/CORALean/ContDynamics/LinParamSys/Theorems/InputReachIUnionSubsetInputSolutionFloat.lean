module

public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `inputSolutionFloat` holds the particulate reachable set of a whole interval matrix

`inputReach_iUnion_subset_inputSolution` in floats: [1, Prop. 2] in its corrected form, at every
member `A` of the float interval matrix and every `t ∈ [0, Δt]`. The time point `Δt` is
`inputReach_subset_inputSolutionFloat`, and `0 ∈ V` brings every earlier time up to it
(`inputReach_mono`); the powers are formed as `𝒜·𝒜ᵏ`, as in the real theorem.

## Inputs
* `sys` – system
* `Δt` – step size
* `η` – Taylor order
* `V` – input zonotope

## Hypotheses
* `hΔt` – step positive
* `hη` – order admissible
* `h0` – origin in the input zonotope

## Conclusion
* every input's contribution, at every member and every time of the step, lies in the enclosure

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.inputReach_iUnion_subset_inputSolutionFloat
    (sys : LinParamSys ℐ[𝕋] n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η) {V : Zonotope (Vec 𝕋 n)}
    (h0 : (0 : Vec ℝ n) ∈ V.construct) : -- --- CONCL ---
    (⋃ A ∈ sys.A.construct, ⋃ t ∈ Set.Icc (0:ℝ) (toReal Δt),
        (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒵[𝕋]) V t)
      ⊆ (sys.inputSolutionFloat Δt η V).construct := by -- --- PROOF ---
  simp only [Set.iUnion_subset_iff]
  intro A hA t ht
  -- `0 ∈ V`: what the input reaches by `t` it can still reach by `Δt`
  refine ((LinearSys.canonical A : LinearSys ℝ n).inputReach_mono (S := 𝒵[𝕋])
    (CompactSet.isBounded_construct V) h0 ht.1 ht.2).trans ?_
  -- the time point `Δt` at the member `A`, inside the float enclosure
  exact sys.inputReach_subset_inputSolutionFloat hΔt hη hA V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
