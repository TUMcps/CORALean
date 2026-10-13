module

public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinStepAtFloatOuter

@[expose] public section

/-!
# One float re-linearization step holds every run of the real system

`relinStepAtFloat_outer` at the expansion point `linPointFloat` computes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]`
from `R` under inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatModel.Encloses.relinStepFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} {R Rτ Rt : Zonotope (Vec 𝕋 n)}
    (hstep : fm.relinStepFloat U options R = some (Rτ, Rt)) :
    0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (toReal options.Δt))
        R.construct U.construct x u →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.construct) ∧
        x (toReal options.Δt) ∈ Rt.construct :=
  h.relinStepAtFloat_outer hstep

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
