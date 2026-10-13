import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
import CORALean.HybridDynamics.Parallel.Operations.ProductWith
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A shared stay is a stay of the product

For any flow with `FlowLaw`. The derivative of the stack is the stack of the derivatives, and by
the flow law each is the product's flow: a state-bound input is the matrix term, a global one the
product's input. The invariant and the input set are the lifted ones, by `Lifting`'s two fields.
Nothing else of the product is read, and no bound input is asked to lie anywhere but where its
component's own location put it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of every component, inputs as bound, is one stay of the product, whose state is the
stack and whose input is `globalInput`. -/
theorem ParallelHybridAutomaton.Stay.trajectoryWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    (hF : P.FlowLaw F) (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) {ℓ : ∀ i, L i}
    {τ : ℝ} {x u : ∀ i, ℝ → Vec ℝ (n i)} {g : ℝ → Vec ℝ m} (h : P.Stay ℓ τ x u g) :
    ((P.productWith lift F).loc ℓ).Trajectory τ (fun t => stack fun i => x i t)
      (fun t => stack (globalInput P.binds fun i => u i t)) where
  nonneg := h.nonneg
  input t ht := by
    show _ ∈ construct (lift.input _)
    exact lift.mem_input _ (fun i => u i t) fun i => h.input i t ht
  flow t ht := by
    -- the stack is differentiable coordinate by coordinate, each coordinate a component's
    classical
    rw [hasDerivWithinAt_pi]
    intro p
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    have hs : ∀ (y : ∀ i, Vec ℝ (n i)) (c : Fin k) (s : Fin (n c)),
        stack y (finSigmaFinEquiv ⟨c, s⟩) = y c s := by
      intro y c s; unfold stack; rw [Equiv.symm_apply_apply]
    -- the component's own flow at coordinate `j`
    have hd := hasDerivWithinAt_pi.mp (h.flow i t ht) j
    simp only [hs]
    refine hd.congr_deriv ?_
    -- the merged matrix on the stack, and what the binding says the input is
    have hm := hF ℓ (fun i => x i t) i j
    simp only [Pi.add_apply]
    show _ = (toRealMat (F ℓ).A *ᵥ stack fun i => x i t) _ + _
    rw [hm]
    have hb := h.bound i j t ht
    cases hbd : P.binds i j with
    | global a => simp [hbd, hs, globalInput]
    | state c s => simp [hbd, hs, globalInput] at hb ⊢; rw [hb]
  invariant t ht := lift.mem_inv _ (fun i => x i t) fun i => h.invariant i t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
