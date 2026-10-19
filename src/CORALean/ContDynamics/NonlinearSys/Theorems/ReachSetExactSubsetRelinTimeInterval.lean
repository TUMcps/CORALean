module

public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetExactOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.RelinTimeIntervalOuter

@[expose] public section

/-!
# One computed set encloses the whole reachable set over a step

`relinTimeInterval_outer` restated on `reachSetExact`, and the nonlinear counterpart
of `LinearSys.reachSetExact_subset_timeInterval_inputSolution`: no trajectory and no
input signal appears anywhere in it, and the reachable set at every time of
step `i` — not only at its ends — lies in one computed set.

What survives of the linear statement's hypotheses are properties of each
step's `linInput`, which a representation answers for, and confinement, which
`reachSetExact_confinement_of_subset` answers for from the computed sets. The step
index stays: `relinTimeInterval` is one set per step by construction.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to enclose a whole step at once; for
`reachSetExact_subset_relinReach` where only the step boundaries matter. -/
theorem NonlinearSys.reachSetExact_subset_relinTimeInterval (sys : NonlinearSys n m)
    {T : Set ℝ} (R₀ : S n) (U : S m) {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    (hΔt : 0 < Δt) (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt),
      sys.reachSetExact T R₀ U t ⊆ (steps i).R)
    (q : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (h0 : ∀ i < N, (0 : Vec ℝ n) ∈ construct (steps i).linInput)
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    {o : ℕ} (ho : 0 < o) (i : ℕ) (hi : i < N)
    {t : ℝ} (ht : t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt)) : -- --- CONCL ---
    sys.reachSetExact T R₀ U t ⊆ construct (sys.relinTimeInterval o ho Δt (q + 2) steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt (q + 2)
        (steps i).linInput) R₀ i) := by -- --- PROOF ---
  rintro _ ⟨x, u, traj, rfl⟩
  exact traj.relinTimeInterval_outer hΔt hT
    (fun j hj s hs => hR j hj s hs (traj.reachSetExact_outer s)) q hε hconv hclosed hbdd h0
    hRconv hRclosed hRbdd ho i hi ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
