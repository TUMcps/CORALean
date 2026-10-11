import CORALean.HybridDynamics.Parallel.Theorems.StayOfTrajectoryWith
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

/-!
# Every run of the product is a parallel run

The converse of `Run.toProductWith`, for any flow with `FlowLaw`, by the product run's recursion.
A stay is `Stay.ofTrajectoryWith`; a jump of the product is a lifted transition of some component
`c` (the merged list is the components' lifted lists), whose guard comes back through
`Lifting.Exact` and whose reset is the update, by `liftTransition_reset`, of the blocks of the
stacked state.

The conditions are those under which the product loses nothing: `Lifting.Exact` (the lifted sets
are not larger than the components' put together), `GlobalsDistinct` (no global input feeds two
coordinates, which the product has no way to equate), `InputsGlobalOnly` (the product's input is
zero where a state is bound), and the flow law (`SelfBindFree` for `mergeFlows`). Without the
second and third the product has more runs than the parallel automaton.
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

/-- A run of the product is a run of the parallel automaton, on the blocks of its states. -/
theorem ParallelHybridAutomaton.Run.ofProductWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    (hF : P.FlowLaw F) (hdist : P.GlobalsDistinct)
    {lift : ParallelHybridAutomaton.Lifting S G n m P.binds}
    (hex : lift.Exact) (hglob : P.InputsGlobalOnly lift) {ℓ ℓ' : ∀ i, L i}
    {z w : Vec ℝ (∑ i, n i)} (run : (P.productWith lift F).Run ℓ z ℓ' w) :
    P.Run ℓ (unstack z) ℓ' (unstack w) := by -- --- PROOF ---
  induction run with
  | @flow ℓ₁ τ X W h =>
    obtain ⟨x, u, g, hst, hx⟩ := ParallelHybridAutomaton.Stay.ofTrajectoryWith hF hdist hex hglob h
    have h0 : (fun i => x i 0) = unstack (X 0) := funext fun i => by rw [hx i]
    have hτ : (fun i => x i τ) = unstack (X τ) := funext fun i => by rw [hx i]
    rw [← h0, ← hτ]
    exact ParallelHybridAutomaton.Run.flow (P := P) hst
  | @jump ℓ₁ ℓ₂ τ X W Y e h hmem hguard rest ih =>
    obtain ⟨x, u, g, hst, hx⟩ := ParallelHybridAutomaton.Stay.ofTrajectoryWith hF hdist hex hglob h
    have h0 : (fun i => x i 0) = unstack (X 0) := funext fun i => by rw [hx i]
    have hτ : (fun i => x i τ) = unstack (X τ) := funext fun i => by rw [hx i]
    -- the product's transition is a component's, lifted
    obtain ⟨c, -, e₀, he₀, rfl⟩ : ∃ c ∈ List.finRange k,
        ∃ e₀ ∈ ((P.comp c).loc (ℓ₁ c)).trans,
          ParallelHybridAutomaton.liftTransition lift ℓ₁ c e₀ = e := by
      obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp hmem
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact ⟨c, hc, e₀, he₀, rfl⟩
    have hg : x c τ ∈ construct e₀.guard := by
      refine hex.guard_inv c e₀.guard (fun i => x i τ) ?_
      rw [hτ, stack_unstack]
      exact hguard
    have hr : (ParallelHybridAutomaton.liftTransition lift ℓ₁ c e₀).reset (X τ) =
        stack (Function.update (fun i => x i τ) c (e₀.reset (x c τ))) := by
      have := ParallelHybridAutomaton.liftTransition_reset lift ℓ₁ c e₀ (fun i => x i τ)
      rwa [show stack (fun i => x i τ) = X τ by rw [hτ, stack_unstack]] at this
    rw [hr, unstack_stack] at ih
    rw [← h0]
    exact ParallelHybridAutomaton.Run.jump (P := P) hst he₀ hg ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
