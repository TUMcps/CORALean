module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterInputSolution
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Definitions.ConvexSet

@[expose] public section

/-!
# Reachability at any convex, compact representation

`reach_outer_inputSolution` with its six topological hypotheses read off the representation instead
of supplied per use. `ConvexSet` and `CompactSet` are quantified over every element of the family,
which is what covers the remainder product as well as `U`: `mtimes` at an interval matrix lands back
in `S n`, so the same two instances answer for both. Six hypotheses from two fields: over a normed
space compactness is closedness and boundedness together, and `CompactSet` proves both once. No
representation is named here. `Zonotope` and `ConZonotope` get their own statement by instantiating
this, and any later one does the same.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `Δt` – sampling step
* `η` – Taylor order
* `o` – zonotope order
* `k` – step index

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hΔt` – step length positive
* `hT` – time domain contains the nonnegative reals
* `hε` – scaled norm small enough for the Taylor order
* `ho` – zonotope order positive

## Conclusion
* the trajectory's sample lies in the sampled reach set at every sample time
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every trajectory of a linear system whose input set is convex and compact
stays in `reach`, at every sample time — so over all of forward time, the
bounded-horizon form being `reach_outer_horizon_inputSolution`. -/
theorem LinearSys.IsCanonicalTrajectory.reach_outer_convexCompact [Mtimes ℐ S]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {o : ℕ} (ho : 0 < o)
    (k : ℕ) : -- --- CONCL ---
    x (k * Δt) ∈ construct
      ((sys.discretize Δt).reach ⟨R₀, sys.inputSolution Δt η U, 0, k⟩ ⟨o, ho⟩) :=
  traj.reach_outer_inputSolution hΔt hT η hε
    (ConvexSet.convex_construct U) (CompactSet.isClosed_construct U)
    (CompactSet.isBounded_construct U)
    (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
    (CompactSet.isBounded_construct _) ho k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
