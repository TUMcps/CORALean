import CORALean.ContDynamics.NeurNetContrSys.Theorems.HoldsOfReach
import CORALean.Specification.Theorems.CheckSound

/-!
# A passed check on the sampled loop's reachable set holds along it

`holds_of_reach` with its hypothesis discharged by running `Specification.check` on the
set `reach` computed, through the pair's `Contains` or `IsDisjoint`: a `true`, found by
evaluation, is the specification on the exact state, with nothing left to prove by hand.
At the period boundaries, since that is where `reach` has anything to say.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    (sys : NeurNetContrSys 𝕋 S n) (o η N : ℕ) (ho : 0 < o) {Δt : ℝ} (hΔt : 0 < Δt)
    (hε : ‖Δt • toRealMat sys.plant.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ} {R₀ : S n}
    {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x : ℝ → Vec ℝ n} (traj : sys.Trajectory π ((N : ℝ) * Δt) H R₀ x)
    (spec : Specification ContSet) (i : ℕ) (hi : i ≤ H) :
    spec.check (sys.reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) →
      (spec.Holds {x ((i : ℝ) * ((N : ℝ) * Δt))}) :=
  fun h => sys.holds_of_reach o η N ho hΔt hε hπ traj spec i hi (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
