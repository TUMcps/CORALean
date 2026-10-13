module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat

@[expose] public section

/-!
# The error solution of the adaptive scheme, in floats

`errorSolutionAdaptive` computed in `𝕋`: CORA's `errorSolution_adaptive` [1, Alg. 2],
`⊕ᵢ₌₀^η Aⁱ Δt^{i+1}/(i+1)! Vdyn ⊕ E Δt Vdyn` plus `eAtInt Vstat` for a static set, with the
float order boxes (`inputTaylorSumFloat`), the float remainder box
`intervalInputRemainder`, which holds `adaptiveRemainder`, and the float `adaptiveIntegral`.
Without a static set this is `inputSolutionFloat` itself.

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

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Rerror` of `errorSolution_adaptive`, line by line, in floats. -/
def LinearSys.errorSolutionAdaptiveFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ)
    (Vdyn : Zonotope (Vec 𝕋 n)) (Vstat : Option (Zonotope (Vec 𝕋 n))) : Zonotope (Vec 𝕋 n) :=
  let AVsum := sys.inputTaylorSumFloat Δt Vdyn η                     -- ∑ᵢ Aⁱ Δt^{i+1}/(i+1)! Vdyn
  let F := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalInputRemainder (Interval.point sys.A) Δt η) Vdyn  -- E Vdyn Δt
  match Vstat with
  | none => AVsum ⊞ F                                                -- AVsum + F
  | some Vs => (AVsum ⊞ F) ⊞ Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.adaptiveIntegral (Interval.point sys.A) Δt η) Vs       -- ... + eAtInt Vstat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
