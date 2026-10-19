module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Pointwise

@[expose] public section

/-!
# Four cells of `[1, Table 1 (⊕)]` fail at the empty set

The paper makes `∅` degenerate and bounded, and `ℝⁿ` is non-degenerate and unbounded, yet
`∅ ⊕ ℝⁿ = ∅` is neither. So "D ⊕ ND = ND", "D ⊕ NB = NB", "ND ⊕ B = ND" and "B ⊕ NB = NB" are
false as printed; `add_properties` has each with a nonempty summand.

## Inputs
* none

## Hypotheses
* `hn` – `0 < n`

## Conclusion
* sets exist whose sum is bounded with empty interior though one summand is unbounded

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

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem add_properties_counterexample (hn : 0 < n) :
    ∃ S₁ S₂ : Set (Vec ℝ n), interior S₁ = ∅ ∧ Bornology.IsBounded S₁ ∧
      (interior S₂).Nonempty ∧ ¬ Bornology.IsBounded S₂ ∧
      interior (S₁ + S₂) = ∅ ∧ Bornology.IsBounded (S₁ + S₂) := by -- --- PROOF ---
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨∅, Set.univ, interior_empty, Bornology.isBounded_empty, ?_,
    NormedSpace.unbounded_univ ℝ _, ?_, ?_⟩
  · rw [interior_univ]
    exact Set.univ_nonempty
  · rw [Set.empty_add, interior_empty]
  · rw [Set.empty_add]
    exact Bornology.isBounded_empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
