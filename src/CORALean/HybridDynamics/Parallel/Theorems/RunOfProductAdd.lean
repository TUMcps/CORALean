import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductWith
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddFlowLaw
import CORALean.HybridDynamics.Parallel.Operations.ProductAdd

/-!
# Every run of `productAdd` is a parallel run, with no `SelfBindFree`

`Run.ofProduct` for the product whose matrix is summed; `Lifting.Exact`, `GlobalsDistinct` and
`InputsGlobalOnly` remain.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.Run.ofProductAdd [ExactScalar 𝕋] [ExactAdd 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hdist : P.GlobalsDistinct)
    {lift : ParallelHybridAutomaton.Lifting S G n m P.binds} (hex : lift.Exact)
    (hglob : P.InputsGlobalOnly lift) {ℓ ℓ' : ∀ i, L i} {z w : Vec ℝ (∑ i, n i)}
    (run : (P.productAdd lift).Run ℓ z ℓ' w) :
    P.Run ℓ (unstack z) ℓ' (unstack w) :=
  ParallelHybridAutomaton.Run.ofProductWith P.mergeFlowsAdd_flowLaw hdist hex hglob run

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
