module

public import CORALean.ContDynamics.NonlinDASys.Operations.Basic

@[expose] public section

/-!
# `ContDynamics/NonlinDASys/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==============================  `NonlinDASys.Trajectory.y_eq`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open ContSet

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- The constraint and `unique`: the only solution of `g(x, ·, u) = 0` is `h x u`. -/
theorem NonlinDASys.Trajectory.y_eq {sys : NonlinDASys n p m} (red : sys.ReducedModel)
    {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory T R₀ U x y u) {t : ℝ} (ht : t ∈ T) : y t = red.h (x t) (u t) :=
  red.unique _ _ _ (traj.constraint t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
