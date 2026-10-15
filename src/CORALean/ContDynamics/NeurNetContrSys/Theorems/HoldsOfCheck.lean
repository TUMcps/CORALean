module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
public import CORALean.Specification.Theorems.CheckSound

@[expose] public section

/-!
# A passed check on the sampled loop's reachable set holds along it

`holds_of_reach` with its hypothesis discharged by running `Specification.check` on the
set `reach` computed, through the pair's `Contains` or `IsDisjoint`: a `true`, found by
evaluation, is the specification on the exact state, with nothing left to prove by hand.
At the period boundaries, since that is where `reach` has anything to say.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) (U_ext : S sys.nExt) (o η N : ℕ) (ho : 0 < o)
    {Δt : ℝ} (hΔt : 0 < Δt) (hdt : sys.dt = (N : ℝ) * Δt)
    (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ} {R₀ : S n}
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.IsTrajectory π H R₀ (construct U_ext) W x v w)
    (spec : Specification ContSet) (i : ℕ) (hi : i ≤ H) :
    spec.check (sys.reach U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) →
      (spec.Holds {x ((i : ℝ) * sys.dt)}) :=
  fun h => sys.holds_of_reach U_ext o η N ho hΔt hdt hε hπ hW traj spec i hi (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
