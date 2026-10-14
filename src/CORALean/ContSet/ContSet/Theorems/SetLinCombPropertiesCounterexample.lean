module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Four cells of `[1, Table 1 (conv)]` fail at the empty set

Under [1, Table 3]'s `conv(S₁, S₂) = {λ s₁ + (1 - λ) s₂}`, `conv(∅, ℝⁿ) = ∅`: `∅` is degenerate
and bounded, `ℝⁿ` non-degenerate and unbounded, and the result is neither. So "D conv ND = ND",
"D conv NB = NB", "ND conv B = ND" and "B conv NB = NB" are false as printed.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem setLinComb_properties_counterexample (hn : 0 < n) :
    ∃ S₁ S₂ : Set (Vec ℝ n), interior S₁ = ∅ ∧ Bornology.IsBounded S₁ ∧
      (interior S₂).Nonempty ∧ ¬ Bornology.IsBounded S₂ ∧
      interior (Set.linComb S₁ S₂) = ∅ ∧
        Bornology.IsBounded (Set.linComb S₁ S₂) := by -- --- PROOF ---
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hseg : Set.linComb (∅ : Set (Vec ℝ n)) Set.univ = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨_, hy, _⟩ => hy
  refine ⟨∅, Set.univ, interior_empty, Bornology.isBounded_empty, ?_,
    NormedSpace.unbounded_univ ℝ _, ?_, ?_⟩
  · rw [interior_univ]
    exact Set.univ_nonempty
  · rw [hseg, interior_empty]
  · rw [hseg]
    exact Bornology.isBounded_empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
