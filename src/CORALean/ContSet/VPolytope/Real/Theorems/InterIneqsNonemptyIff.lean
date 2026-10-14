module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# Does a V-polytope meet an H-polytope?

[1, Eq. 14]: exactly when the linear program [1, Eq. 15] is feasible — a convex combination of
the points satisfying the inequalities.

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

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.inter_ineqs_nonempty_iff (P : VPolytope (Vec ℝ n)) (A : Mat ℝ q n)
    (b : Vec ℝ q) :
    (P.construct ∩ (HPolytope.ineqs A b).construct).Nonempty ↔
      ∃ (x : Vec ℝ n) (β : Fin P.k → ℝ), A *ᵥ x ≤ b ∧ ∑ j, β j • P.V j = x ∧
        ∑ j, β j = 1 ∧ ∀ j, 0 ≤ β j := by -- --- PROOF ---
  constructor
  · rintro ⟨x, ⟨β, hβ, s, rfl⟩, hx⟩
    exact ⟨_, β, fun i => HPolytope.mem_ineqs_iff.mp hx i, rfl, s, hβ⟩
  · rintro ⟨x, β, hx, rfl, s, hβ⟩
    exact ⟨_, ⟨β, hβ, s, rfl⟩, HPolytope.mem_ineqs_iff.mpr hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
