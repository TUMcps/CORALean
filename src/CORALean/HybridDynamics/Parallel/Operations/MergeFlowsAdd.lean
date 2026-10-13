import CORALean.Global.ExactAdd
import CORALean.HybridDynamics.Parallel.Operations.MergeFlows

/-!
# `mergeFlowsAdd`

`mergeFlows` with CORA's `Amerged += B * C` as an addition: the block-diagonal matrix of the
components' `A`, plus a `1` at row `⟨i, j⟩`, column `⟨c, s⟩` for each input `binds i j = state c s`.
Where the bound state is a state of the coordinate's own component, the entry is `A_js + 1`, which
`mergeFlows` cannot form without an exact sum and so replaces by `1`, valid only under
`SelfBindFree`. Here the sum is formed, so the flow law (`mergeFlowsAdd_mulVec`) holds with no
hypothesis. It needs `ExactAdd`, which holds at `ℝ` and at no float scalar.
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

def ParallelHybridAutomaton.mergeFlowsAdd [ExactScalar 𝕋] [ExactAdd 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) (ℓ : ∀ i, L i) : LinearSys 𝕋 (∑ i, n i) where
  A := Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun a b =>
    (if h : a.1 = b.1 then ((P.comp a.1).loc (ℓ a.1)).dynamics.A a.2
        (Fin.cast (congrArg n h.symm) b.2) else 0) +
    (match P.binds a.1 a.2 with
      | .global _ => 0
      | .state c s => if (⟨c, s⟩ : Σ i, Fin (n i)) = b then 1 else 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
