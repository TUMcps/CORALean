module

public import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw

@[expose] public section

/-!
# A shared stay is a stay of the product

`Stay.trajectoryWith` at `mergeFlows`, whose flow law holds under `SelfBindFree`
(`mergeFlows_flowLaw`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of every component, inputs as bound, is one stay of the product, whose state is the
stack and whose input is `globalInput`. -/
theorem ParallelHybridAutomaton.Stay.trajectory [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hself : P.SelfBindFree)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) {ℓ : ∀ i, L i} {τ : ℝ}
    {x u : ∀ i, ℝ → Vec ℝ (n i)} {g : ℝ → Vec ℝ m} (h : P.Stay ℓ τ x u g) :
    (P.locationProduct lift ℓ).Trajectory τ (fun t => stack fun i => x i t)
      (fun t => stack (globalInput P.binds fun i => u i t)) :=
  h.trajectoryWith (P.mergeFlows_flowLaw hself) lift

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
