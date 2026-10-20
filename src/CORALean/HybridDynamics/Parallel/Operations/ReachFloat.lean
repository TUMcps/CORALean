module

public import CORALean.HybridDynamics.Parallel.Operations.ProductWith
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeDistSets
public import CORALean.HybridDynamics.Operations.ReachFloat
public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# Parallel hybrid automata in floats: CORA's `parallelHybridAutomaton/reach`

CORA computes the reachable set of a parallel automaton as that of its product. Here the product is
`productWith` at `mergeFlows`, the merged flow assembled without arithmetic (exact at a float scalar
where the components are state-bound), with `mergeInputSets` and `mergeDistSets`; it is run by
`HybridAutomaton.reachFloat`, from the float zonotope of the stacked initial states, at the float
zonotope and halfspace families; the `Lifting` that stacks the components' invariants, guards,
inputs and disturbances is supplied. Soundness is `ParallelHybridAutomaton.reachFloat_outer`.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `tFinal` – final time
* `options` – reach options
* `K` – jump depth
* `ℓ` – initial locations
* `X₀` – initial zonotope

## Output
* location-tagged reach sets of the product, none on failure
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-interval sets of every run of the product from `X₀` at `ℓ` with at most `K` jumps and
stays of at most `tFinal`, each paired with its location tuple. -/
def ParallelHybridAutomaton.reachFloat
    (P : ParallelHybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) n m)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : ∀ i, L i)
    (X₀ : Zonotope (Vec 𝕋 (∑ i, n i))) : Option (List ((∀ i, L i) × Zonotope (Vec 𝕋 (∑ i, n i)))) :=
  (P.productWith lift P.mergeFlows (P.mergeInputSets lift) (P.mergeDistSets lift)).reachFloat
    tFinal options K ℓ X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
