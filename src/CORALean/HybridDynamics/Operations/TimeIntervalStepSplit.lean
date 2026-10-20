module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.HybridDynamics.Operations.InputSet
public import CORALean.HybridDynamics.Operations.TimeIntervalStep

@[expose] public section

/-!
# `Location.timeIntervalStepSplit`

The stay enclosure with the input contribution computed rather than named, at a location whose
combined input set `ℓ.inputSet = B U ⊕ c ⊕ E W` need not hold the origin. `Recenter` takes it
apart into a center and a remainder around zero, as CORA's `canonicalForm` does: the center
travels as a constant through `expIntegral` and `constCorrectionMatrix`, and `inputSolution` sees
only the remainder. The set is that of `timeIntervalStep ⊞ inputSolution ℓ.inputSet` where
`0 ∈ ℓ.inputSet` already; this is `TimeIntervalOuterSplit`'s form, which a location can supply.

## Inputs
* `ℓ` – location
* `r` – time step
* `η` – Taylor order
* `X₀` – initial set

## Output
* stay enclosure with split input
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stay enclosure over `X₀`, the input contribution split into the center
of `ℓ.inputSet` and the remainder around zero. -/
noncomputable def Location.timeIntervalStepSplit [∀ n, OfPoint (S n) (Vec ℝ n)]
    [∀ n, Recenter (S n) (Vec ℝ n)] (ℓ : Location S G L 𝕋 n) (r : ℝ) (η : ℕ) (X₀ : S n) : S n :=
  Plus.plus (ℓ.timeIntervalStep r η X₀)
    (Plus.plus
      (Plus.plus
        (Mtimes.mtimes (𝕄 := Mat ℝ)
          (MatExp.expIntegral (toRealMat ℓ.dynamics.A) r)
          (LinComb.linComb (OfPoint.ofPoint (0 : Vec ℝ n))
            (OfPoint.ofPoint (Recenter.center ℓ.inputSet))))
        (Mtimes.mtimes (𝕄 := ℐ)
          (MatExp.constCorrectionMatrix (toRealMat ℓ.dynamics.A) r η)
          (OfPoint.ofPoint (Recenter.center ℓ.inputSet))))
      (ℓ.dynamics.inputSolution r η (Recenter.recenter ℓ.inputSet)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
