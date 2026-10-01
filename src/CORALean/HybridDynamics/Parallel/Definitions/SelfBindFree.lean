import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

/-!
# Where `mergeFlows` is exact

`mergeFlows` builds the product's matrix with no arithmetic, so a coordinate bound to a state of
its *own* component gets a `1` where CORA's `A + B * C` would add `1` to the component's `A_ij`.
Those agree when `A_ij = 0`, and `SelfBindFree` is that: no coordinate is bound to a state of its
own component at which the component's `A` is nonzero. A binding to another component's state
needs no hypothesis, the block being `0` there (#117).
A user with a self-binding at a nonzero `A_ij` can still use the product by folding the
self-loop into the component's own `A` before building the parallel automaton.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No `A_ij + 1` is ever needed: see the module docstring. With a self-binding at a nonzero `A_ij`,
fold the self-loop into the component's own `A` before building the parallel automaton. -/
def ParallelHybridAutomaton.SelfBindFree (P : ParallelHybridAutomaton S G k L 𝕋 n m) : Prop :=
  ∀ (ℓ : ∀ i, L i) (i : Fin k) (j : Fin (n i)) (s : Fin (n i)), P.binds i j = .state i s →
    toRealMat ((P.comp i).loc (ℓ i)).dynamics.A j s = 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
