module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ToNonlinearSys
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-!
# A parametric trajectory is its combined-input embedding's

`Fin.append (u t) (p t)` is the combined input at `t`; `hW` is what makes it
land in `construct W`, there being no cartesian-product class on `ContSet` to
build `W` from `U` and `P` instead. `Fin.append_left`/`_right` read the two
halves back out of it, which is what turns `sys.toNonlinearSys.f` at that input
into `sys.f (x t) (u t) (p t)`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.IsTrajectory.toNonlinearSys {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {W : S (m + q)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {p : ℝ → Vec ℝ q} {y : ℝ → Vec ℝ sys.r} (traj : sys.IsTrajectory T R₀ U P x u p y)
    (hW : ∀ v ∈ construct U, ∀ w ∈ construct P, Fin.append v w ∈ construct W) : -- --- CONCL ---
    sys.toNonlinearSys.IsTrajectory T R₀ W x
      (fun t => Fin.append (u t) (p t)) y := by -- --- PROOF ---
  -- the field read through the stacked input is the parameterized one
  have he : (fun t => sys.toNonlinearSys.f (x t) (Fin.append (u t) (p t)))
      = fun t => sys.f (x t) (u t) (p t) := by
    funext t
    have hu : Fin.append (u t) (p t) ∘ Fin.castAdd q = u t := funext (Fin.append_left (u t) (p t))
    have hp : Fin.append (u t) (p t) ∘ Fin.natAdd m = p t := funext (Fin.append_right (u t) (p t))
    simp only [NonlinParamSys.toNonlinearSys, hu, hp]
  refine ⟨traj.init, fun t ht => hW (u t) (traj.input t ht) (p t) (traj.param t ht), ?_,
    fun t ht => ?_, traj.cont, fun t ht => ?_, fun t ht => ?_⟩
  · rw [he]; exact traj.meas
  · rw [he]; exact traj.integrable t ht
  · rw [he]; exact traj.flow t ht
  · -- the output map read through the stacked input is the parameterized one
    have hu : Fin.append (u t) (p t) ∘ Fin.castAdd q = u t := funext (Fin.append_left (u t) (p t))
    have hp : Fin.append (u t) (p t) ∘ Fin.natAdd m = p t := funext (Fin.append_right (u t) (p t))
    rw [traj.output t ht]
    simp only [NonlinParamSys.toNonlinearSys, hu, hp]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
