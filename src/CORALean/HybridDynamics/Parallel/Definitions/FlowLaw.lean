module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# What a product's flow must do to a stack

The one property of a product's flow `F`, input sets `U` and disturbance sets `W` that the passage
from parallel to product runs reads, at every location tuple and every instant: for states `x`,
inputs `u` that obey the bindings, global inputs `g` that the components' input sets admit and
disturbances `w` in theirs, the product has an input in `U` and a disturbance in `W` under which
coordinate `⟨i, a⟩` of its right-hand side at the stack of `x` is component `i`'s own
`Aᵢ xᵢ + Bᵢ uᵢ + cᵢ + Eᵢ wᵢ` at `a`. `mergeFlowsLinearSys` has it at `ℝ` under `FeedthroughFree`
(`product_flowLaw`); the run theorems are stated for any flow that has it.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.FlowLaw (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)) (U : ∀ ℓ, S (F ℓ).m) (W : ∀ ℓ, S (F ℓ).r) :
    Prop :=
  ∀ (ℓ : ∀ i, L i) (x : ∀ i, Vec ℝ (n i)) (u : ∀ i, Vec ℝ (P.sys ℓ i).m)
    (w : ∀ i, Vec ℝ (P.sys ℓ i).r) (g : Vec ℝ m),
    (∀ i j, u i j = P.boundInput ℓ x u g i j) →
    (∀ i, ∃ v ∈ construct ((P.comp i).loc (ℓ i)).U, ∀ j a, P.bindsAt ℓ i j = .global a →
      v j = g a) →
    (∀ i, w i ∈ construct ((P.comp i).loc (ℓ i)).W) →
    ∃ (g' : Vec ℝ (F ℓ).m) (w' : Vec ℝ (F ℓ).r), g' ∈ construct (U ℓ) ∧ w' ∈ construct (W ℓ) ∧
      ∀ i a, (toRealMat (F ℓ).A *ᵥ stack x + toRealMat (F ℓ).B *ᵥ g' + toRealVec (F ℓ).c +
        toRealMat (F ℓ).E *ᵥ w') (finSigmaFinEquiv ⟨i, a⟩) =
        (toRealMat (P.sys ℓ i).A *ᵥ x i + toRealMat (P.sys ℓ i).B *ᵥ u i +
          toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ w i) a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
