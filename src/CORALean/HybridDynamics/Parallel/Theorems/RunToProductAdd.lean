import CORALean.HybridDynamics.Parallel.Theorems.RunToProductWith
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddFlowLaw
import CORALean.HybridDynamics.Parallel.Operations.ProductAdd

/-!
# Every parallel run is a run of `productAdd`, with no `SelfBindFree`

`Run.toProduct` for the product whose matrix is summed: a coordinate bound to a state of its own
component at a nonzero `A_ij` is covered, which `product` covers only under `SelfBindFree`.
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

theorem ParallelHybridAutomaton.Run.toProductAdd [ExactScalar 𝕋] [ExactAdd 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m}
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) {ℓ ℓ' : ∀ i, L i}
    {x y : ∀ i, Vec ℝ (n i)} (run : P.Run ℓ x ℓ' y) :
    (P.productAdd lift).Run ℓ (stack x) ℓ' (stack y) :=
  ParallelHybridAutomaton.Run.toProductWith P.mergeFlowsAdd_flowLaw lift run

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
