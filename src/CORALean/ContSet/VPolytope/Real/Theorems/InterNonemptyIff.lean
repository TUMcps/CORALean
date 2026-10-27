module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# Do two V-polytopes intersect?

[1, Eq. 11]: exactly when the linear program [1, Eq. 12] is feasible — two convex combinations,
one of each point list, meeting in one point.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* none

## Conclusion
* the polytopes meet iff two convex combinations of the vertices agree

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.inter_nonempty_iff (P₁ P₂ : VPolytope α) : -- --- CONCL ---
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
