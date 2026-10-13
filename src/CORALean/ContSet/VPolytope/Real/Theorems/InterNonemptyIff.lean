import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# Do two V-polytopes intersect?

[1, Eq. 11]: exactly when the linear program [1, Eq. 12] is feasible — two convex combinations,
one of each point list, meeting in one point.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.inter_nonempty_iff (P₁ P₂ : VPolytope α) :
    (P₁.construct ∩ P₂.construct).Nonempty ↔
      ∃ (β₁ : Fin P₁.k → ℝ) (β₂ : Fin P₂.k → ℝ), ∑ j, β₁ j • P₁.V j = ∑ l, β₂ l • P₂.V l ∧
        ∑ j, β₁ j = 1 ∧ (∀ j, 0 ≤ β₁ j) ∧ ∑ l, β₂ l = 1 ∧ ∀ l, 0 ≤ β₂ l := by -- --- PROOF ---
  constructor
  · rintro ⟨x, ⟨β₁, h₁, s₁, rfl⟩, ⟨β₂, h₂, s₂, e₂⟩⟩
    exact ⟨β₁, β₂, e₂, s₁, h₁, s₂, h₂⟩
  · rintro ⟨β₁, β₂, e, s₁, h₁, s₂, h₂⟩
    exact ⟨_, ⟨β₁, h₁, s₁, rfl⟩, ⟨β₂, h₂, s₂, e⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
