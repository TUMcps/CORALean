import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

/-!
# No global input feeds two coordinates

The product keeps one input *per coordinate* (`globalInput` stacks the components' inputs), where
CORA's product has the global input vector itself. When two coordinates are bound to the same
global input `a`, a product input may give them different values, which no parallel run does: the
product then has behaviours the parallel automaton lacks. `GlobalsDistinct` rules that out, each
global input feeding at most one coordinate, and is what the converse of `Run.toProduct` assumes
(or else the product's input set would have to enforce the equalities, which no `Lifting` here
does).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.GlobalsDistinct (P : ParallelHybridAutomaton S G k L 𝕋 n m) : Prop :=
  ∀ (i i' : Fin k) (j : Fin (n i)) (j' : Fin (n i')) (a : Fin m),
    P.binds i j = .global a → P.binds i' j' = .global a →
      (⟨i, j⟩ : Σ i, Fin (n i)) = ⟨i', j'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
