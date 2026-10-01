import CORALean.HybridDynamics.Parallel.Theorems.RunToProduct
import CORALean.HybridDynamics.Theorems.RunOuter

/-!
# An invariant of the product bounds a parallel run

`HybridAutomaton.Run.mem_of_invariant` at the product, through `Run.toProduct`: whatever
`Invariant` the single automaton is given, discharged by the single automaton's own theorems
(`FlowOuter`, `JumpOuter`), encloses every run of the parallel one, stacked. The outer
reachable set of a parallel automaton is the single automaton's, with no new analysis.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stack of a parallel run's end state is in the invariant's set, given its start. -/
theorem ParallelHybridAutomaton.Run.mem_of_invariant [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hself : P.SelfBindFree)
    {lift : ParallelHybridAutomaton.Lifting S G n m P.binds}
    {R : (∀ i, L i) → S (∑ i, n i)} (hinv : (P.product lift).Invariant R)
    {ℓ ℓ' : ∀ i, L i} {x y : ∀ i, Vec ℝ (n i)} (run : P.Run ℓ x ℓ' y)
    (hx : stack x ∈ construct (R ℓ)) : stack y ∈ construct (R ℓ') :=
  (run.toProduct hself lift).mem_of_invariant hinv hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
