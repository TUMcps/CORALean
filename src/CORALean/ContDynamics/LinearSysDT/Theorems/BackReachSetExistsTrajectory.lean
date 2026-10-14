module

public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetExists
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate

@[expose] public section

/-!
# From the backward reachable set, a run into the target exists

What makes `backReachSetExists` deserve the name, and it cannot be
`backReachSetForall_trajectory`'s statement: there the run is given and the
conclusion is about it, here the input signal is what the set asserts, so the
theorem *produces* one. From `x₀` in the `k`-step set comes a signal admissible
for the `k` steps that matter, whose run is in `T` at step `k`.

`TrajectoryOn k` and not `Trajectory`: past step `k` nothing was chosen, and an
empty `U` admits no total signal at all while `backReachSetExists T U 0` is
still `T`. `R₀` enters only through `init`, from the caller's `hx₀`.

`aux_simulate_cons` is the shift the induction needs — `backReachSetExists`
peels a step off the front, so the signal is built by prepending — and
`aux_backReachSetExists_input` is the run without `R₀`, which is what lets the
induction move to a start state no set was named for.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step of `simulate` taken off the front: running `u` from `x₀` is running
its tail from the state the first input produced. -/
theorem LinearSysDT.aux_simulate_cons (sys : LinearSysDT 𝕋 n) (x₀ : Vec ℝ n)
    (u : ℕ → Vec ℝ n) (j : ℕ) : sys.simulate x₀ u (j + 1) =
      sys.simulate (toRealMat sys.A *ᵥ x₀ + u 0) (fun i => u (i + 1)) j := by
  induction j with
  | zero => rfl
  | succ j ih => show toRealMat sys.A *ᵥ sys.simulate x₀ u (j + 1) + u (j + 1) = _; rw [ih]; rfl

/-- The signal alone, with no `R₀` and so nothing tying the start state to a
set: what the induction on `k` needs, since the state one step in lies in no set
the statement mentions. -/
theorem LinearSysDT.aux_backReachSetExists_input (sys : LinearSysDT 𝕋 n) (T U : S n) (k : ℕ) :
    ∀ x₀ ∈ sys.backReachSetExists T U k, ∃ u : ℕ → Vec ℝ n,
      (∀ j < k, u j ∈ construct U) ∧ sys.simulate x₀ u k ∈ construct T := by -- --- PROOF ---
  induction k with
  | zero => exact fun x₀ hx => ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero j), hx⟩
  | succ k ih =>
    rintro x₀ ⟨u₀, hu₀, hx₁⟩
    obtain ⟨v, hv, hT⟩ := ih _ hx₁
    -- the chosen input in front of the signal the remaining steps produced
    refine ⟨fun j => match j with | 0 => u₀ | i + 1 => v i, ?_, ?_⟩
    · rintro (_ | i) hj
      · exact hu₀
      · exact hv i (by omega)
    · rw [sys.aux_simulate_cons]
      exact hT


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachSetExists_trajectory (sys : LinearSysDT 𝕋 n) (T U : S n)
    {R₀ : S n} {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) (k : ℕ)
    (hx : x₀ ∈ sys.backReachSetExists T U k) :
    ∃ u : ℕ → Vec ℝ n, sys.TrajectoryOn R₀ U k (sys.simulate x₀ u) u ∧
      sys.simulate x₀ u k ∈ construct T := by
  obtain ⟨u, hu, hT⟩ := sys.aux_backReachSetExists_input T U k x₀ hx
  exact ⟨u, ⟨hx₀, hu, fun _ _ => rfl⟩, hT⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
