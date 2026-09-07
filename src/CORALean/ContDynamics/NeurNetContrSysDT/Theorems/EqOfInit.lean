import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

/-!
# Determinism: the initial state settles the run

The controller is a function, so the loop is deterministic and `Trajectory`
carries no information beyond `x 0 ∈ R₀`. Stated in the form normally wanted:
whichever initial sets the two runs were taken from, agreeing at step zero
settles them everywhere, via `aux_eq_iterate` identifying each with the orbit
of `map` at its own starting point.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem NeurNetContrSysDT.Trajectory.aux_eq_iterate {sys : NeurNetContrSysDT 𝕋 S n} {R₀ : S n}
    {π : Vec ℝ n → Vec ℝ n} {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    x k = (sys.map π)^[k] (x 0) := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, traj.step k]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- Determinism, in the form it is normally wanted: the initial state settles
the run, whichever initial sets the two runs were taken from. -/
theorem NeurNetContrSysDT.Trajectory.eq_of_init {sys : NeurNetContrSysDT 𝕋 S n} {R₀ R₁ : S n}
    {π : Vec ℝ n → Vec ℝ n} {x y : ℕ → Vec ℝ n} (hx : sys.Trajectory π R₀ x)
    (hy : sys.Trajectory π R₁ y) (h : x 0 = y 0) : x = y := by
  funext k
  rw [hx.aux_eq_iterate k, hy.aux_eq_iterate k, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
