import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution

/-!
# `relinReach` encloses the reachable set at the step boundaries

`relinReach_outer_inputSolution` restated on `reachSet`: what it says of every
run at `iΔt`, this says of the set of them at once, so a specification about
the reachable set meets the loop's enclosure as a single inclusion.

Confinement is asked of `reachSet` rather than of a run, which is the only
change to the hypotheses and the whole point of the restatement — nothing here
mentions `x` or `u`, and `reachSet_confinement_of_subset` supplies `hR` from a
check on the computed sets.

Between the boundaries this says nothing; that is
`reachSet_subset_relinTimeInterval`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this at the step boundaries; the guarantee attaches to the
reachable set, and the confinement it asks for does too. -/
theorem NonlinearSys.reachSet_subset_relinReach [Mtimes ℐ S] (sys : NonlinearSys n m)
    {T : Set ℝ} (R₀ : S n) (U : S m) {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    (hΔt : 0 < Δt) (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt),
      sys.reachSet T R₀ U t ⊆ (steps i).R)
    (η : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / ((η : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput))) (o : ℕ) :
    ∀ i ≤ N, sys.reachSet T R₀ U ((i : ℝ) * Δt) ⊆ construct (sys.relinReach o Δt steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt η
        (steps i).linInput) R₀ i) := by
  rintro i hi _ ⟨x, u, traj, rfl⟩
  exact traj.relinReach_outer_inputSolution hΔt hT
    (fun j hj t ht => hR j hj t ht (traj.reachSet_outer t)) η hε hconv hclosed hbdd
    hRconv hRclosed hRbdd o i hi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
