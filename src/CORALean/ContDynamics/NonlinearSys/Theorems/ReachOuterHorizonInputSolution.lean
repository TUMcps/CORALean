module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizonInputSolution
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeHorizon

@[expose] public section

/-!
# The nonlinear reachable set over a horizon, the input set named

The same as `reach_outer_horizon`, with the input enclosure named, so no
quantity depending on the trajectory survives into the hypotheses.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
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

theorem NonlinearSys.IsTrajectory.reach_outer_horizon_inputSolution [Mtimes ℐ S]
    {sys : NonlinearSys n m} {T : Set ℝ} {R₀ L : S n} {U : S m} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ m} {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n}
    {us : Vec ℝ m} {R : Set (Vec ℝ n)} {Δt : ℝ} {K : ℕ} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory T R₀ U x u y)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) ((K : ℝ) * Δt), x t ∈ R) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct (linInput sys.f A B xs us U L)))
    (hclosed : IsClosed (construct (linInput sys.f A B xs us U L)))
    (hbdd : Bornology.IsBounded (construct (linInput sys.f A B xs us U L)))
    -- the next three are asked of the remainder's product, `R(τ)` varying with `τ`
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (linInput sys.f A B xs us U L))))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (linInput sys.f A B xs us U L))))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) (linInput sys.f A B xs us U L)))) {o : ℕ}
    (ho : 0 < o) : -- --- STMT ---
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct
      (((NonlinearSys.linearize A).discretize Δt).reach
        ⟨R₀, (NonlinearSys.linearize A).inputSolution Δt η (linInput sys.f A B xs us U L), 0, k⟩
        ⟨o, ho⟩) :=
  (traj.linearize_horizon cert hT hR).reach_outer_horizon_inputSolution hΔt subset_rfl η hε
    hconv hclosed hbdd hRconv hRclosed hRbdd ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
