module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton
public import CORALean.Global.ExactScalar

@[expose] public section

/-!
# What a product's flow must do to a stack

The one property of the product's matrix that the passage between parallel and product runs
reads: applied to the stack of the components' states, coordinate `⟨i, j⟩` is component `i`'s own
flow plus, where `binds i j` is a state, that state. `mergeFlows` has it under `SelfBindFree`
(`mergeFlows_mulVec`), `mergeFlowsAdd` without a hypothesis (`mergeFlowsAdd_mulVec`); the run
theorems are stated for any flow that has it, so each is proved once for both.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.FlowLaw (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)) : Prop :=
  ∀ (ℓ : ∀ i, L i) (x : ∀ i, Vec ℝ (n i)) (i : Fin k) (j : Fin (n i)),
    (toRealMat (F ℓ).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, j⟩) =
      (toRealMat ((P.comp i).loc (ℓ i)).dynamics.A *ᵥ x i) j +
      (match P.binds i j with
        | .global _ => 0
        | .state c s => x c s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
