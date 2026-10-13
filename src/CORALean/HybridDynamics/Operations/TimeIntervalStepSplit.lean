import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.HybridDynamics.Operations.TimeIntervalStep

/-!
# `Location.timeIntervalStepSplit`

The stay enclosure with the input contribution computed rather than named, at a
location whose input set need not hold the origin. `Recentre` takes `ℓ.U` apart
into a centre and a remainder around zero: the centre travels as a constant
through `expIntegral` and `constCorrectionMatrix`, and `inputSolution` sees only
the remainder, which does hold the origin.

`timeIntervalStep ⊞ inputSolution ℓ.U` is the same set where `0 ∈ ℓ.U` already;
this is `TimeIntervalOuterSplit`'s form, which asks nothing about where `ℓ.U`
sits and so is the one a location can actually supply.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
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

/-- The stay enclosure over `X₀`, the input contribution split into the centre
of `ℓ.U` and the remainder around zero. -/
noncomputable def Location.timeIntervalStepSplit [∀ n, OfPoint (S n) (Vec ℝ n)]
    [∀ n, Recentre (S n) (Vec ℝ n)] (ℓ : Location S G L 𝕋 n) (r : ℝ) (η : ℕ) (X₀ : S n) : S n :=
  Plus.plus (ℓ.timeIntervalStep r η X₀)
    (Plus.plus
      (Plus.plus
        (Mtimes.mtimes (𝕄 := Mat ℝ)
          (MatExp.expIntegral (toRealMat ℓ.dynamics.A) r)
          (LinComb.linComb (OfPoint.ofPoint (0 : Vec ℝ n))
            (OfPoint.ofPoint (Recentre.centre ℓ.U))))
        (Mtimes.mtimes (𝕄 := ℐ)
          (MatExp.constCorrectionMatrix (toRealMat ℓ.dynamics.A) r η)
          (OfPoint.ofPoint (Recentre.centre ℓ.U))))
      (ℓ.dynamics.inputSolution r η (Recentre.recentre ℓ.U)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
