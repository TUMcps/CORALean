module

public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLaw
public import CORALean.HybridDynamics.Parallel.Operations.LocationProduct

@[expose] public section

/-!
# A shared stay is a stay of the product

`IsStay.trajectoryWith` at `mergeFlowsLinearSys`, whose flow law holds at `ℝ` under
`FeedthroughFree` (`mergeFlowsLinearSys_flowLaw`).

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `ℓ` – current locations
* `τ` – stay duration
* `x` – component trajectories
* `u` – component inputs
* `w` – component disturbances
* `g` – global input

## Hypotheses
* `hfeed` – no feedthrough between bound outputs
* `h` – shared stay of the components

## Conclusion
* the stacked stay is a trajectory of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of every component, inputs as bound, is one stay of the product location, whose state
is the stack, under some input and disturbance of the product. -/
theorem ParallelHybridAutomaton.IsStay.trajectory {P : ParallelHybridAutomaton S G k L ℝ n m}
    (hfeed : P.FeedthroughFree) (lift : ParallelHybridAutomaton.Lifting S G n m)
    {ℓ : ∀ i, L i} {τ : ℝ} {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m}
    (h : P.IsStay ℓ τ x u w g) :
    ∃ (g' : ℝ → Vec ℝ m) (w' : ℝ → Vec ℝ (∑ i, (P.sys ℓ i).r)),
      (P.locationProduct lift ℓ).IsTrajectory τ (fun t => stack fun i => x i t) g' w' :=
  h.trajectoryWith (P.mergeFlowsLinearSys_flowLaw hfeed lift) lift

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
