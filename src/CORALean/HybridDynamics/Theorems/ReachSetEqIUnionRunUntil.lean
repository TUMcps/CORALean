import CORALean.HybridDynamics.Definitions.ReachSet
import CORALean.HybridDynamics.Theorems.RunIffExistsRunUntil

/-!
# The reachable set, sliced by duration and jump count

`reachSet` is the union, over every duration bound `T` and jump count `k`, of
the states reached by runs lasting at most `T` with `k` jumps — the run-level
`run_iff_exists_runUntil` read at the set `reachSet` names. A slice `T ≤ tFinal`,
`k ≤ K` of this union is what `reachSet_subset_reachFloat` encloses.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.reachSet_eq_iUnion_runUntil (HA : HybridAutomaton S G L 𝕋 n)
    (R₀ : S n) (ℓ₀ ℓ : L) :
    HA.reachSet R₀ ℓ₀ ℓ
      = ⋃ (T : ℝ) (k : ℕ),
        {y | ∃ x ∈ construct R₀, HA.RunUntil T k ℓ₀ x ℓ y} := by -- --- PROOF ---
  ext y
  simp only [HybridAutomaton.reachSet, Set.mem_setOf_eq, Set.mem_iUnion,
    HybridAutomaton.run_iff_exists_runUntil]
  constructor
  · rintro ⟨x, hx, T, k, run⟩
    exact ⟨T, k, x, hx, run⟩
  · rintro ⟨T, k, x, hx, run⟩
    exact ⟨x, hx, T, k, run⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
