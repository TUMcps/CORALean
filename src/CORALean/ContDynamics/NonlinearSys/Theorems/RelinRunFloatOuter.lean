import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunFloat
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinRunAtFloatOuter

/-!
# The float re-linearization loop holds every run of the real system

`relinRunAtFloat_outer` at the expansion points `linPointFloat` computes.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k` successful steps return `k` sets, and every run of `sys` on `[0, kΔt]` from
`R` under inputs in `U` is, at every time of step `j`, in the `j`-th of them: the
re-linearization loop at its own `linPointFloat`. -/
theorem NonlinearSys.FloatModel.Encloses.relinRunFloat_outer
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachOptions 𝕋} :
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {Rs : List (Zonotope (Vec 𝕋 n))},
      fm.relinRunFloat U options k R = some Rs → Rs.length = k ∧
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m},
          sys.Trajectory (S := fun k => Set (Vec ℝ k))
            (Set.Icc 0 ((k : ℝ) * toReal options.timeStep)) R.construct U.construct x u →
          ∀ (j : ℕ) (hj : j < Rs.length), ∀ t ∈ Set.Icc ((j : ℝ) * toReal options.timeStep)
            (((j : ℝ) + 1) * toReal options.timeStep), x t ∈ Rs[j].construct :=
  fun k _ _ hrun => h.relinRunAtFloat_outer k hrun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
