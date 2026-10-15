module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map

@[expose] public section

/-!
# At a linear plant, a run is an orbit of `map`

A `Trajectory` of the closed loop at a `LinearSysDT`, its disturbance in a `W` that `E` sends to
`0`, starts in `R₀` and steps by `map`: `A x + B π(x) + c`, the plant's own equation with `E w`
gone. This is what every guarantee at a linear plant reads a run through, as CORA's loop, which
drops `E`, computes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with a disturbance `E` sends to `0` starts in `R₀` and steps by `map`. -/
theorem NeurNetContrSysDT.Trajectory.linear {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n}
    {π : Vec ℝ n → Vec ℝ sys.plant.m} {R₀ : S n} {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {w : ℕ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π R₀ W x w) :
    x 0 ∈ construct R₀ ∧ ∀ k, x (k + 1) = sys.map π (x k) := by -- --- PROOF ---
  obtain ⟨v, y, tr⟩ := traj
  refine ⟨tr.init, fun k => ?_⟩
  -- the plant's step, its disturbance term `0`
  rw [tr.step k, hW _ (tr.dist k), add_zero]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
