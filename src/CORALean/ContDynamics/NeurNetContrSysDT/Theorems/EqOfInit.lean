module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.IsTrajectoryLinear

@[expose] public section

/-!
# Determinism: the initial state and the external input settle the run

The controller is a function, so the loop is deterministic up to its external input: `IsTrajectory`
carries no information beyond `x 0 ∈ R₀` and `v ∈ U_ext`. Stated in the form normally wanted:
whichever initial sets and disturbance sets the two runs were taken from, agreeing at step zero
and under the same external input they agree everywhere, via `aux_eq_simulate` identifying each
with `simulate` at its own starting point.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem NeurNetContrSysDT.IsTrajectory.aux_eq_simulate
    {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n} {R₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {π : Vec ℝ n → Vec ℝ sys.m} {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π R₀ U_ext W x v w) (k : ℕ) :
    x k = sys.simulate π v (x 0) k := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [(traj.linear hW).2.2 k, ih]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- Determinism, in the form it is normally wanted: the initial state settles the run under a
given external input, whichever initial sets the two runs were taken from. -/
theorem NeurNetContrSysDT.IsTrajectory.eq_of_init
    {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n} {R₀ R₁ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {π : Vec ℝ n → Vec ℝ sys.m} {W₀ W₁ : Set (Vec ℝ sys.plant.r)}
    (hW₀ : ∀ v ∈ W₀, toRealMat sys.plant.E *ᵥ v = 0)
        (hW₁ : ∀ v ∈ W₁, toRealMat sys.plant.E *ᵥ v = 0)
    {x y : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt} {w₀ w₁ : ℕ → Vec ℝ sys.plant.r}
    (hx : sys.IsTrajectory π R₀ U_ext W₀ x v w₀) (hy : sys.IsTrajectory π R₁ U_ext W₁ y v w₁)
    (h : x 0 = y 0) : x = y := by -- --- PROOF ---
  funext k
  rw [hx.aux_eq_simulate hW₀ k, hy.aux_eq_simulate hW₁ k, h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
