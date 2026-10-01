import CORALean.HybridDynamics.Parallel.Theorems.StayTrajectory
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

/-!
# Every parallel run is a run of the product

The soundness direction, by the run's own recursion: a stay is `Stay.trajectory`, a jump of
component `c` is the lifted transition's jump, in the list by construction, its guard met by
`Lifting.mem_guard` and its reset the update by `liftTransition_reset`. The states are stacked
and the locations are the tuples, so nothing is converted on the way.

Only this direction: a run of the product may let the components disagree on a bound input,
having no one to check them, so the converse is not claimed (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the parallel automaton, its states stacked, is a run of its product. -/
theorem ParallelHybridAutomaton.Run.toProduct [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m}
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) {ℓ ℓ' : ∀ i, L i}
    {x y : ∀ i, Vec ℝ (n i)} (run : P.Run ℓ x ℓ' y) :
    (P.product lift).Run ℓ (stack x) ℓ' (stack y) := by -- --- PROOF ---
  -- one case per constructor, as the run's recursion has it
  induction run with
  | flow h => exact HybridAutomaton.Run.flow (HA := P.product lift) (h.trajectory lift)
  | @jump ℓ₁ ℓ₂ τ x u g y c e h hmem hguard rest ih =>
    refine HybridAutomaton.Run.jump (HA := P.product lift)
      (e := ParallelHybridAutomaton.liftTransition lift ℓ₁ c e) (h.trajectory lift) ?_ ?_ ?_
    · -- the lifted transition is in the merged list
      exact List.mem_flatMap.mpr ⟨_, List.mem_finRange _, List.mem_map.mpr ⟨_, hmem, rfl⟩⟩
    · exact lift.mem_guard _ _ (fun i => _) hguard
    · rw [ParallelHybridAutomaton.liftTransition_reset]
      exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
