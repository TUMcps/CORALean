module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# No global input feeds two inputs

The product's input set is a set of global-input vectors, built from the components' input sets.
When two inputs are bound to the same global input `a`, the lifted set can only take `a`'s range
from one of them, and so may admit a value the other component's set rules out: the product then
has behaviours the parallel automaton lacks. `GlobalsDistinct` rules that out, each global input
feeding at most one input, and is what the converse of `IsRun.toProduct` assumes.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S G : ℕ → Type} {𝕋 : Type} {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.GlobalsDistinct (P : ParallelHybridAutomaton S G k L 𝕋 n m) : Prop :=
  ∀ (i i' : Fin k) (j : Fin (P.p i)) (j' : Fin (P.p i')) (a : Fin m),
    P.binds i j = .global a → P.binds i' j' = .global a →
      (⟨i, j⟩ : Σ i, Fin (P.p i)) = ⟨i', j'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
