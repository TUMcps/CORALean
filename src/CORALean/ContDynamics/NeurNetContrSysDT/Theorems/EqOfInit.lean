module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryLinear

@[expose] public section

/-!
# Determinism: the initial state settles the run

The controller is a function, so the loop is deterministic and `Trajectory`
carries no information beyond `x 0 ∈ R₀`. Stated in the form normally wanted:
whichever initial sets the two runs were taken from, agreeing at step zero
settles them everywhere, via `aux_eq_iterate` identifying each with the orbit
of `map` at its own starting point.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem NeurNetContrSysDT.Trajectory.aux_eq_iterate
    {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n} {R₀ : S n}
    {π : Vec ℝ n → Vec ℝ sys.plant.m} {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {w : ℕ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π R₀ W x w) (k : ℕ) :
    x k = (sys.map π)^[k] (x 0) := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, (traj.linear hW).2 k]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Determinism, in the form it is normally wanted: the initial state settles
the run, whichever initial sets the two runs were taken from. -/
theorem NeurNetContrSysDT.Trajectory.eq_of_init
    {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n} {R₀ R₁ : S n}
    {π : Vec ℝ n → Vec ℝ sys.plant.m} {W₀ W₁ : Set (Vec ℝ sys.plant.r)}
    (hW₀ : ∀ v ∈ W₀, toRealMat sys.plant.E *ᵥ v = 0)
        (hW₁ : ∀ v ∈ W₁, toRealMat sys.plant.E *ᵥ v = 0)
    {x y : ℕ → Vec ℝ n} {w₀ w₁ : ℕ → Vec ℝ sys.plant.r} (hx : sys.Trajectory π R₀ W₀ x w₀)
    (hy : sys.Trajectory π R₁ W₁ y w₁) (h : x 0 = y 0) : x = y := by -- --- PROOF ---
  funext k
  rw [hx.aux_eq_iterate hW₀ k, hy.aux_eq_iterate hW₁ k, h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
