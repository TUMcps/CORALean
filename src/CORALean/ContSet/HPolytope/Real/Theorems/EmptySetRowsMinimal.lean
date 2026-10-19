module

public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet
public import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet

@[expose] public section

/-!
# The one-row H-representation of `∅` has the fewest rows

[1, Sec. 3 (minimal representation)]: "empty sets are ... in minimal representation". For halfspaces
this holds of CORA's representation of `∅`, the single row `0 ≤ -1` (`HPolytope.emptySet`). No
H-representation of `∅` has fewer rows: with no rows at all, every point satisfies the system. Not
every H-representation of `∅` is minimal (`empty_redundant_counterexample`).

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (minimal representation)]: `emptySet` is `∅`, and every H-representation of `∅` has
at least its rows. -/
theorem HPolytope.emptySet_rows_minimal : -- --- CONCL ---
    (HPolytope.emptySet α).construct = ∅ ∧
      ∀ P : HPolytope α, P.construct = ∅ →
        (HPolytope.emptySet α).m + (HPolytope.emptySet α).me
          ≤ P.m + P.me := by -- --- PROOF ---
  refine ⟨HPolytope.construct_emptySet, fun P hP => ?_⟩
  show 1 ≤ P.m + P.me
  by_contra h
  -- no rows: `0` satisfies every one of them, vacuously
  have hm : P.m = 0 := by omega
  have hme : P.me = 0 := by omega
  have h0 : (0 : α) ∈ P.construct :=
    ⟨fun i => absurd i.2 (by omega), fun i => absurd i.2 (by omega)⟩
  rw [hP] at h0
  exact h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
