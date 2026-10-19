module

public import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIffSupportFunc

@[expose] public section

/-!
# Set equality of H-polytopes by mutual containment

[1, Eq. 8]: two H-polytopes are equal exactly when each contains the other, each containment
checked by the support functions of [1, Eq. 5]. Nothing is assumed of either polytope, which is
why the paper uses it for degenerate ones.

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

namespace CORALean.Real

open Matrix

variable {q₁ q₂ n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_eq_iff_supportFunc {A₁ : Mat ℝ q₁ n} {b₁ : Vec ℝ q₁}
    {A₂ : Mat ℝ q₂ n} {b₂ : Vec ℝ q₂} : -- --- CONCL ---
    (HPolytope.ineqs A₁ b₁).construct = (HPolytope.ineqs A₂ b₂).construct ↔
      (∀ j, supportFunc (HPolytope.ineqs A₁ b₁).construct (HPolytope.rowLin A₂ j) ≤ (b₂ j : EReal))
        ∧ ∀ j, supportFunc (HPolytope.ineqs A₂ b₂).construct (HPolytope.rowLin A₁ j)
          ≤ (b₁ j : EReal) := by -- --- PROOF ---
  rw [Set.Subset.antisymm_iff, HPolytope.ineqs_subset_iff_supportFunc,
    HPolytope.ineqs_subset_iff_supportFunc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
