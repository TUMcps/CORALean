module

public import CORALean.ContDynamics.NonlinearSys.Operations.CenterAbstrRunFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinRunFloatOuter

@[expose] public section

/-!
# The float run linearized at the center holds every run of the real system

`relinRunAtFloat_outer` at `x✱ = center(R)` for each step's start set.
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

/-- `k` successful steps return `k` sets, and every run of `sys` on `[0, kΔt]` from `R`
under inputs in `U` is, at every time of step `j`, in the `j`-th of them. -/
theorem NonlinearSys.FloatModel.Encloses.centerAbstrRunFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} :
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {Rs : List (Zonotope (Vec 𝕋 n))},
      fm.centerAbstrRunFloat U options k R = some Rs → Rs.length = k ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := 𝒮)
            (Set.Icc 0 ((k : ℝ) * toReal options.Δt)) R.construct U.construct x u y →
          ∀ (j : ℕ) (hj : j < Rs.length), ∀ t ∈ Set.Icc ((j : ℝ) * toReal options.Δt)
            (((j : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[j].construct :=
  fun k _ _ hrun => h.relinRunAtFloat_outer k hrun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
