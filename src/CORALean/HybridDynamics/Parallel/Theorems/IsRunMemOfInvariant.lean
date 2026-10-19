module

public import CORALean.HybridDynamics.Parallel.Theorems.IsRunToProduct
public import CORALean.HybridDynamics.Theorems.IsRunOuter

@[expose] public section

/-!
# An invariant of the product bounds a parallel run

`HybridAutomaton.IsRun.mem_of_invariant` at the product, through `IsRun.toProduct`: whatever
`Invariant` the single automaton is given, discharged by the single automaton's own theorems
(`FlowOuter`, `JumpOuter`), encloses every run of the parallel one, stacked. The outer
reachable set of a parallel automaton is the single automaton's, with no new analysis.
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

/-- The stack of a parallel run's end state is in the invariant's set, given its start. -/
theorem ParallelHybridAutomaton.IsRun.mem_of_invariant {P : ParallelHybridAutomaton S G k L ℝ n m}
    (hfeed : P.FeedthroughFree) {lift : ParallelHybridAutomaton.Lifting S G n m}
    {R : (∀ i, L i) → S (∑ i, n i)} (hinv : (P.product lift).Invariant R)
    {ℓ ℓ' : ∀ i, L i} {x y : ∀ i, Vec ℝ (n i)} (run : P.IsRun ℓ x ℓ' y)
    (hx : stack x ∈ construct (R ℓ)) : -- --- STMT ---
    stack y ∈ construct (R ℓ') :=
  (run.toProduct hfeed lift).mem_of_invariant hinv hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
