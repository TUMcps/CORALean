import CORALean.HybridDynamics.Parallel.Operations.Product
import CORALean.HybridDynamics.Operations.ReachFloat
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# Parallel hybrid automata in floats: CORA's `parallelHybridAutomaton/reach`

CORA computes the reachable set of a parallel automaton as that of its product. Here the product
(`ParallelHybridAutomaton.product`, generic over the scalar) is run by
`HybridAutomaton.reachFloat`, from the float zonotope of the stacked initial states, at the float
zonotope and halfspace families; the `Lifting` that stacks the components' invariants, guards and
inputs is supplied. Soundness is `ParallelHybridAutomaton.reachFloat_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-interval sets of every run of the product from `X₀` at `ℓ` with at most `K` jumps and
stays of at most `tFinal`, each paired with its location tuple. -/
def ParallelHybridAutomaton.reachFloat
    (P : ParallelHybridAutomaton (Zonotope 𝕋) (HPolytope 𝕋) k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting (Zonotope 𝕋) (HPolytope 𝕋) n m P.binds)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : ∀ i, L i)
    (X₀ : Zonotope 𝕋 (∑ i, n i)) : Option (List ((∀ i, L i) × Zonotope 𝕋 (∑ i, n i))) :=
  (P.product lift).reachFloat tFinal options K ℓ X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
