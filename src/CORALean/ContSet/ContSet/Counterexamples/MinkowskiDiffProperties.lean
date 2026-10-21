module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Four cells of `[1, Table 1 (⊖)]` fail at the empty subtrahend

`∅` is empty, degenerate and bounded in the paper's convention, and `∅ ⊖ ∅ = ℝⁿ` by
[1, Table 3]. So "E ⊖ D = E", "E ⊖ B = E", "B ⊖ D = B" and "B ⊖ B = B" are false as printed;
`minkowskiDiff_properties` has each with a nonempty subtrahend.

## Inputs
* none

## Hypotheses
* `hn` – `0 < n`

## Conclusion
* sets exist whose Minkowski difference is nonempty and unbounded

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
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

theorem minkowskiDiff_properties_counterexample (hn : 0 < n) : -- --- CONCL ---
    ∃ S₁ S₂ : Set (Vec ℝ n), S₁ = ∅ ∧ Bornology.IsBounded S₁ ∧ interior S₂ = ∅ ∧
      Bornology.IsBounded S₂ ∧ minkowskiDiff S₁ S₂ ≠ ∅ ∧
      ¬ Bornology.IsBounded (minkowskiDiff S₁ S₂) := by -- --- PROOF ---
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have huniv : minkowskiDiff (∅ : Set (Vec ℝ n)) ∅ = Set.univ :=
    Set.eq_univ_of_forall fun _ _ hy => hy.elim
  refine ⟨∅, ∅, rfl, Bornology.isBounded_empty, interior_empty, Bornology.isBounded_empty, ?_, ?_⟩
  · rw [huniv]
    exact Set.univ_nonempty.ne_empty
  · rw [huniv]
    exact NormedSpace.unbounded_univ ℝ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
