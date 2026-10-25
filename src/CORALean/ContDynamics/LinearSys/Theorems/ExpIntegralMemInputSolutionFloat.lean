module

public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat

@[expose] public section

/-!
# A constant input's contribution lies in `inputSolutionFloat`

CORA's `affineSolution` and the constant-input `particularSolution` hold the input (and the
affine offset) at one value `u` of the set `V` and integrate the exponential against it:
`expIntegral A Δt · u`. That is one of the inputs `inputReach` ranges over, so it lies in the
float enclosure `inputSolutionFloat` of it, by `inputReach_subset_inputSolutionFloat`. Route a:
outer over every input in `V`, the constant input included; the hypothesis on the step is the
float order's admissibility, as in that theorem.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `V` – input float zonotope
* `uc` – constant input

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `huc` – constant input lies in the zonotope

## Conclusion
* a constant input's contribution lies in the float input solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.expIntegral_mem_inputSolutionFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η) (V : Zonotope (Vec 𝕋 n))
    {uc : Vec ℝ n} (huc : uc ∈ V.construct) :
    Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) *ᵥ uc
      ∈ (sys.inputSolutionFloat Δt η V).construct :=
  sys.inputReach_subset_inputSolutionFloat hΔt hη V
    (sys.expIntegral_mem_inputReach (S := 𝒵[𝕋]) hΔt.le huc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
