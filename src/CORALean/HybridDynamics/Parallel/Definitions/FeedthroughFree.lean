module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# No output that feeds an input passes an output-bound input through

CORA's `aux_mergeFlowsLinearSys` refuses a feeding output whose feedthrough `D` reads an input
that is itself bound to an output: "this would otherwise lead to infinite loops" (an algebraic
loop). `FeedthroughFree` is that check, at every location tuple: where input `j` of component `i`
reads output `s` of component `c`, the entry `D_c(s, j')` is zero at every input `j'` of `c` bound
to an output. Under it the bound inputs are the merged system's, `mergeFlowsLinearSys_flow`.

## Inputs
* `P` – parallel automaton

## Output
* no output feeding an input passes an output-bound input through
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar

variable {S G : ℕ → Type} {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.FeedthroughFree (P : ParallelHybridAutomaton S G k L 𝕋 n m) : Prop :=
  ∀ (ℓ : ∀ i, L i) i j c s, P.bindsAt ℓ i j = .output c s →
    ∀ j' c' s', P.bindsAt ℓ c j' = .output c' s' → toReal ((P.sys ℓ c).D s j') = 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
