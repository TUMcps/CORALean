module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum

@[expose] public section

/-!
# The error solution of the adaptive scheme

CORA's `errorSolution_adaptive` [1, Alg. 2] for a dynamic input set `Vdyn` and, if there
is one, a static set `Vstat`: `⊕ᵢ₌₀^η Aⁱ Δt^{i+1}/(i+1)! Vdyn ⊕ E Δt Vdyn`, plus
`eAtInt Vstat` for the static part, with the interval matrices of `adaptiveRemainder` and
`adaptiveIntegral`. The order `η` is a parameter; CORA's own choice of it is
`errorSolutionOrder`.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order
* `Vdyn` – dynamic noise set
* `Vstat` – optional static noise set

## Output
* error solution set of the adaptive scheme

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Rerror` of `errorSolution_adaptive`, line by line. -/
noncomputable def LinearSys.errorSolutionAdaptive (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ)
    (Vdyn : S n) (Vstat : Option (S n)) : S n :=
  let AVsum := sys.inputTaylorSum Δt Vdyn η                          -- ∑ᵢ Aⁱ Δt^{i+1}/(i+1)! Vdyn
  let F := Mtimes.mtimes (𝕄 := ℐ)
    (MatExp.adaptiveRemainder (toRealMat sys.A) Δt η) Vdyn          -- E Vdyn Δt
  match Vstat with
  | none => Plus.plus AVsum F                                        -- AVsum + F
  | some Vs => Plus.plus (Plus.plus AVsum F) (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.adaptiveIntegral (toRealMat sys.A) Δt η) Vs)           -- ... + eAtInt Vstat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
