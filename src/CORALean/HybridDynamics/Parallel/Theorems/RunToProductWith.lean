import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectoryWith
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

/-!
# Every parallel run is a run of the product

For any flow with `FlowLaw`; the soundness direction, by the run's own recursion: a stay is
`Stay.trajectory`, a jump of component `c` is the lifted transition's jump, in the list by
construction, its guard met by `Lifting.mem_guard` and its reset the update by
`liftTransition_reset`. The states are stacked and the locations are the tuples, so nothing is
converted on the way.

Only this direction: a run of the product may let the components disagree on a bound input,
having no one to check them, so the converse is not claimed (#40).
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

/-- A run of the parallel automaton, its states stacked, is a run of the product with flow `F`. -/
theorem ParallelHybridAutomaton.Run.toProductWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    (hF : P.FlowLaw F) (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) {ℓ ℓ' : ∀ i, L i}
    {x y : ∀ i, Vec ℝ (n i)} (run : P.Run ℓ x ℓ' y) :
    (P.productWith lift F).Run ℓ (stack x) ℓ' (stack y) := by -- --- PROOF ---
  -- one case per constructor, as the run's recursion has it
  induction run with
  | flow h => exact HybridAutomaton.Run.flow (HA := P.productWith lift F) (h.trajectoryWith hF lift)
  | @jump ℓ₁ ℓ₂ τ x u g y c e h hmem hguard rest ih =>
    refine HybridAutomaton.Run.jump (HA := P.productWith lift F)
      (e := ParallelHybridAutomaton.liftTransition lift ℓ₁ c e) (h.trajectoryWith hF lift) ?_ ?_ ?_
    · -- the lifted transition is in the merged list
      exact List.mem_flatMap.mpr ⟨_, List.mem_finRange _, List.mem_map.mpr ⟨_, hmem, rfl⟩⟩
    · exact lift.mem_guard _ _ (fun i => _) hguard
    · rw [ParallelHybridAutomaton.liftTransition_reset]
      exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
