module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinementOfSubset

@[expose] public section

/-!
# Confinement of the whole reachable set, from the computed sets

`confinement_of_subset` with the trajectory quantifier gone rather than moved:
its hypotheses name no run, so what it says of each run over step `i` it says
of `reachSet` over step `i`, as one set inside the region step `i`'s
certificate was issued for.

That is what the downstream statements need. `relinTimeInterval_outer` asks
confinement of `x`, which only a run has; asking it of `reachSet` instead is a
condition on `R₀`, `U` and `steps` alone, and this theorem discharges even that
from the ball check `hsub` — inflate each computed set by `ρ > MΔt` and ask it
to lie in that step's region.

The certified regions `(steps i).R` are arbitrary sets, not a representation,
so the conclusion is `Set` inclusion and no operation class answers for it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
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
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point the flow reaches during step `i` lies in step `i`'s certified
region, on the strength of a check on the computed sets: no trajectory appears
in the hypotheses and none appears in the conclusion. -/
theorem NonlinearSys.reachSet_confinement_of_subset [Mtimes ℐ S] (sys : NonlinearSys n m)
    {T : Set ℝ} (R₀ : S n) (U : S m) {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    {M ρ : ℝ} (hΔt : 0 < Δt) (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (η : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / ((η : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hM₀ : 0 ≤ M) (hM : ∀ i < N, ∀ y ∈ (steps i).R, ∀ v ∈ construct U, ‖sys.f y v‖ ≤ M)
    (hρ : M * Δt < ρ) {o : ℕ} (ho : 0 < o)
    (hsub : ∀ i < N, ∀ y ∈ construct (sys.relinReach ⟨R₀, 0, i⟩ ⟨Δt, o, ho⟩ steps (fun i =>
      (NonlinearSys.linearize (steps i).A).inputSolution Δt η (steps i).linInput)),
      Metric.closedBall y ρ ⊆ (steps i).R) : -- --- STMT ---
    ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt),
      sys.reachSet T R₀ U t ⊆ (steps i).R := by -- --- PROOF ---
  rintro i hi t ht _ ⟨x, u, traj, rfl⟩
  exact traj.confinement_of_subset hΔt hT η hε hconv hclosed hbdd hRconv hRclosed hRbdd
    hM₀ hM hρ ho hsub i hi t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
