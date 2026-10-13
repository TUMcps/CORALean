import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrStepFloat
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinStepFloatOuter

/-!
# One float step linearized at the centre holds every run of the real system

`relinStepAtFloat_outer` at `x✱ = center(R)`: where a step linearizes is the caller's, a poor
point costing a larger remainder and never soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R`
under inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatModel.Encloses.centreAbstrStepFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} {R Rτ Rt : Zonotope (Vec 𝕋 n)}
    (hstep : fm.centreAbstrStepFloat U options R = some (Rτ, Rt)) :
    0 < toReal options.timeStep ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (toReal options.timeStep))
        R.construct U.construct x u →
      (∀ t ∈ Set.Icc 0 (toReal options.timeStep), x t ∈ Rτ.construct) ∧
        x (toReal options.timeStep) ∈ Rt.construct :=
  h.relinStepAtFloat_outer hstep

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
