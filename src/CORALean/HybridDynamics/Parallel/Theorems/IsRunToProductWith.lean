module

public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

@[expose] public section

/-!
# Every parallel run is a run of the product

For any flow with `FlowLaw`; the soundness direction, by the run's own recursion: a stay is
`IsStay.trajectoryWith`, a jump of component `c` is the lifted transition's jump, in the list by
construction, its guard met by `Lifting.mem_guard` and its reset the update by
`liftTransition_reset`. The states are stacked and the locations are the tuples, so nothing is
converted on the way.

The converse is `IsRun.ofProductWith`, under `FlowLawConverse` and an exact `Lifting`.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the parallel automaton, its states stacked, is a run of the product with flow `F`. -/
theorem ParallelHybridAutomaton.IsRun.toProductWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.FlowLaw F U W)
    (lift : ParallelHybridAutomaton.Lifting S G n m) {ℓ ℓ' : ∀ i, L i}
    {x y : ∀ i, Vec ℝ (n i)} (run : P.IsRun ℓ x ℓ' y) :
    (P.productWith lift F U W).IsRun ℓ (stack x) ℓ' (stack y) := by -- --- PROOF ---
  -- one case per constructor, as the run's recursion has it
  induction run with
  | flow h =>
    obtain ⟨g', w', htr⟩ := h.trajectoryWith hF lift
    exact HybridAutomaton.IsRun.flow (HA := P.productWith lift F U W) htr
  | @jump ℓ₁ ℓ₂ τ x u w g y c e h hmem hguard rest ih =>
    obtain ⟨g', w', htr⟩ := h.trajectoryWith hF lift
    refine HybridAutomaton.IsRun.jump (HA := P.productWith lift F U W)
      (e := ParallelHybridAutomaton.liftTransition lift ℓ₁ c e) htr ?_ ?_ ?_
    · -- the lifted transition is in the merged list
      exact List.mem_flatMap.mpr ⟨_, List.mem_finRange _, List.mem_map.mpr ⟨_, hmem, rfl⟩⟩
    · exact lift.mem_guard _ _ (fun i => _) hguard
    · rw [ParallelHybridAutomaton.liftTransition_reset]
      exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
