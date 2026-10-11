import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectoryWith
import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
import CORALean.HybridDynamics.Parallel.Theorems.UnstackStack
import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
import CORALean.HybridDynamics.Parallel.Definitions.GlobalsDistinct
import CORALean.HybridDynamics.Parallel.Definitions.InputsGlobalOnly

/-!
# A stay of the product is a shared stay

The converse of `Stay.trajectoryWith`, for any flow with `FlowLaw`. Given a stay of the product's
location, the components' states are the blocks of its state; a state-bound input is the state it
is bound to, a global one is the product's input at that coordinate, and `g` reads each global
input off the one coordinate it feeds (`GlobalsDistinct`). The product's input is a stack of a
`globalInput` (`InputsGlobalOnly`), so it is zero at the state-bound coordinates and the merged
matrix supplies the binding term alone, by the flow law. The invariant and the input set come back
through `Lifting.Exact`.

The conditions are the ones a product run can break: nothing in `Location.Trajectory` says the
product's input is zero at a state-bound coordinate, or equal at two coordinates of one global
input.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of the product at `ℓ` is a stay of the components, whose states are the blocks of the
product's state. -/
theorem ParallelHybridAutomaton.Stay.ofTrajectoryWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    (hF : P.FlowLaw F) (hdist : P.GlobalsDistinct)
    {lift : ParallelHybridAutomaton.Lifting S G n m P.binds}
    (hex : lift.Exact) (hglob : P.InputsGlobalOnly lift) {ℓ : ∀ i, L i} {τ : ℝ}
    {X W : ℝ → Vec ℝ (∑ i, n i)} (h : ((P.productWith lift F).loc ℓ).Trajectory τ X W) :
    ∃ (x u : ∀ i, ℝ → Vec ℝ (n i)) (g : ℝ → Vec ℝ m), P.Stay ℓ τ x u g ∧
      (∀ i, x i = fun t => unstack (X t) i) := by -- --- PROOF ---
  classical
  -- the product's input is the stack of a `globalInput`, at each time of the stay
  have hW : ∀ t ∈ Set.Icc 0 τ, ∃ v : ∀ i, Vec ℝ (n i), W t = stack (globalInput P.binds v) :=
    fun t ht => hglob ℓ (W t) (h.input t ht)
  -- the global input `a` is read off the one coordinate it feeds, if any
  let g : ℝ → Vec ℝ m := fun t a =>
    if hp : ∃ p : Σ i, Fin (n i), P.binds p.1 p.2 = .global a then
      unstack (W t) hp.choose.1 hp.choose.2 else 0
  let u : ∀ i, ℝ → Vec ℝ (n i) := fun i t j =>
    match P.binds i j with
    | .global _ => unstack (W t) i j
    | .state c s => unstack (X t) c s
  refine ⟨fun i t => unstack (X t) i, u, g, ?_, fun i => rfl⟩
  have hs : ∀ (y : ∀ i, Vec ℝ (n i)) (c : Fin k) (s : Fin (n c)),
      stack y (finSigmaFinEquiv ⟨c, s⟩) = y c s := by
    intro y c s; unfold stack; rw [Equiv.symm_apply_apply]
  refine ⟨h.nonneg, ?_, ?_, ?_, ?_⟩
  · -- the input: the product's input is a stack, so the components' inputs lie in their sets
    intro i t ht
    obtain ⟨v, hv⟩ := hW t ht
    have hin := hex.input_inv _ v (hv ▸ h.input t ht) i
    have : globalInput P.binds (fun i => u i t) = globalInput P.binds v := by
      funext i' j
      have hj := congrFun (congrFun (congrArg unstack hv) i') j
      rw [unstack_stack] at hj
      simp only [globalInput] at hj ⊢
      simp only [u]
      cases hb : P.binds i' j
      · simp [hb] at hj ⊢
        exact hj
      · simp
    rw [this]
    exact hin
  · -- the flow: coordinate `⟨i, j⟩` of the product's, by the flow law and the binding
    intro i t ht
    obtain ⟨v, hv⟩ := hW t ht
    -- the coordinates of the product's derivative
    have hX := h.flow t ht
    have hX' : ∀ j : Fin (n i), HasDerivWithinAt (fun t => X t (finSigmaFinEquiv ⟨i, j⟩))
        ((toRealMat (F ℓ).A *ᵥ X t + W t) (finSigmaFinEquiv ⟨i, j⟩))
        (Set.Icc 0 τ) t := fun j => hasDerivWithinAt_pi.mp hX _
    rw [hasDerivWithinAt_pi]
    intro j
    refine (hX' j).congr_deriv ?_
    -- the flow law at the stack of the blocks, and the input at this coordinate
    have hm := hF ℓ (fun i => unstack (X t) i) i j
    rw [show stack (fun i => unstack (X t) i) = X t from stack_unstack _] at hm
    rw [Pi.add_apply, hm, Pi.add_apply]
    have hWj : W t (finSigmaFinEquiv ⟨i, j⟩) = globalInput P.binds v i j := by
      rw [hv, hs]
    rw [hWj]
    show _ = _ + u i t j
    simp only [u, globalInput]
    cases hb : P.binds i j with
    | global a =>
      have := congrFun (congrFun (congrArg unstack hv) i) j
      rw [unstack_stack] at this
      simp only [globalInput, hb] at this
      simp only [this, add_zero]
    | state c s => simp
  · -- the invariant, through `Lifting.Exact`
    intro i t ht
    have := hex.inv_inv _ _ (by rw [stack_unstack]; exact h.invariant t ht)
    exact this i
  · -- the binding: a global input is read off the one coordinate it feeds
    intro i j t ht
    obtain ⟨v, hv⟩ := hW t ht
    simp only [u, g]
    cases hb : P.binds i j with
    | global a =>
      have hp : ∃ p : Σ i, Fin (n i), P.binds p.1 p.2 = .global a := ⟨⟨i, j⟩, hb⟩
      dsimp only
      rw [dif_pos hp]
      have := hdist _ _ _ _ _ hb hp.choose_spec
      obtain ⟨hi, hj⟩ := Sigma.mk.inj_iff.mp this
      subst hi
      have hj' := eq_of_heq hj
      subst hj'
      rfl
    | state c s => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
