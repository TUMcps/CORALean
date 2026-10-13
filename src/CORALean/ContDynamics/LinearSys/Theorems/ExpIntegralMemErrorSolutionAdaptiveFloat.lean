module

public import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionAdaptiveFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat

@[expose] public section

/-!
# `errorSolutionAdaptiveFloat` holds what a held input contributes

Without a static set the float error solution is `inputSolutionFloat`, and an input held at
`v ∈ Vdyn` over `[0, Δt]` contributes `∫₀^Δt e^{Aσ}dσ v`, one of the contributions
`inputReach_subset_inputSolutionFloat` encloses. Outer only, held inputs only, as
`expIntegral_mem_errorSolutionAdaptive` is over ℝ; the bound is [1, Lemma 1]'s.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix MeasureTheory

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `Δt > 0` and an order the float enclosures admit, `∫₀^Δt e^{Aσ}dσ v` is in the float
error solution for every `v ∈ Vdyn`. -/
theorem LinearSys.expIntegral_mem_errorSolutionAdaptiveFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋}
    {η : ℕ} (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η)
    {Vdyn : Zonotope (Vec 𝕋 n)} {v : Vec ℝ n} (hv : v ∈ Vdyn.construct) :
    Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ v
      ∈ (sys.errorSolutionAdaptiveFloat Δt η Vdyn none).construct := by -- --- PROOF ---
  -- the input held at `v` is admissible, so its contribution is enclosed
  have hreach : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ v
      ∈ sys.inputReach (S := fun k => Zonotope (Vec 𝕋 k)) Vdyn (toReal Δt) :=
    ⟨fun _ => v, fun _ _ => hv, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput _ v hΔt.le).symm⟩
  exact sys.inputReach_subset_inputSolutionFloat hΔt hη Vdyn hreach

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
