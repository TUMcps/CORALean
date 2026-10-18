module

public import CORALean.ContDynamics.NonlinearSys.Operations.OrderStepFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinStepFloatOuter

@[expose] public section

/-!
# One float step at either abstraction order holds every run of the real system

`relinStepFloat_outer` at `κ = 1` and `linReachFloat_outer` at `'lin'` otherwise: the order only
picks which remainder the step spends. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful step has a positive width, and every run of `sys` on `[0, Δt]` from `R`
under inputs in `U` is in `R(τ)` over the step and in `R(t₁)` at its end. -/
theorem NonlinearSys.FloatHessModel.Encloses.orderStepFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {κ : ℕ} {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋}
    {R Rτ Rt : Zonotope (Vec 𝕋 n)}
    (hstep : fm.orderStepFloat κ U options R = some (Rτ, Rt)) : -- --- STMT ---
    0 < toReal options.Δt ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
      sys.IsTrajectory (S := 𝒮) (Set.Icc 0 (toReal options.Δt))
        R.construct U.construct x u →
      (∀ t ∈ Set.Icc 0 (toReal options.Δt), x t ∈ Rτ.construct) ∧
        x (toReal options.Δt) ∈ Rt.construct := by -- --- PROOF ---
  unfold NonlinearSys.FloatHessModel.orderStepFloat at hstep
  split at hstep
  · exact h.toEncloses.relinStepFloat_outer hstep
  · exact h.linReachFloat_outer hstep

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
