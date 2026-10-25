module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# Where `mergeFlows` is exact

`mergeFlows` builds the product's matrix with no arithmetic, so an input bound to an output of its
*own* component gets a `1` where CORA's `A + B * C` would add `1` to the component's `A` entry.
Those agree when the entry is `0`, and `IsSelfBindFree` is that: at every location tuple, where
input `j` of component `i` is bound to its own output `s`, the entry of `A` at row `j`, column `s`
is zero (`HasStateBound` reads input `j` as state `j` and output `s` as state `s`). A binding to
another component's output needs no hypothesis, the block being `0` there (#117).

## Inputs
* `P` – parallel automaton

## Output
* a self-bound input meets a zero state matrix entry
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar

variable {S G : ℕ → Type} {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No `A_ij + 1` is ever needed: see the module docstring. -/
def ParallelHybridAutomaton.IsSelfBindFree (P : ParallelHybridAutomaton S G k L 𝕋 n m) : Prop :=
  ∀ (ℓ : ∀ i, L i) i (j : Fin (P.sys ℓ i).m) (s : Fin (P.sys ℓ i).q) (p q : Fin (n i)),
    P.bindsAt ℓ i j = .output i s → p.val = j.val → q.val = s.val →
      toReal ((P.sys ℓ i).A p q) = 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
