import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# What the convex hull does to emptiness, degeneracy and boundedness

[1, Table 1 (conv)] with `conv(S₁, S₂) = {λ s₁ + (1 - λ) s₂}` [1, Table 3], which is
`segments`: empty if either operand is; with both nonempty it contains both, so it inherits an
interior and unboundedness from either; bounded operands give a bounded hull. The table also
claims "D conv ND = ND", "D conv NB = NB", "ND conv B = ND" and "B conv NB = NB", which fail at
an empty operand — degenerate and bounded in the paper's convention, and absorbing under this
`conv` (`segments_properties_counterexample`).

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem segments_properties (S₁ S₂ : Set (Vec ℝ n)) :
    (S₁ = ∅ ∨ S₂ = ∅ → segments S₁ S₂ = ∅) ∧
      (S₁.Nonempty → S₂.Nonempty → (segments S₁ S₂).Nonempty) ∧
      (S₁.Nonempty → (interior S₂).Nonempty → (interior (segments S₁ S₂)).Nonempty) ∧
      ((interior S₁).Nonempty → S₂.Nonempty → (interior (segments S₁ S₂)).Nonempty) ∧
      (S₁.Nonempty → ¬ Bornology.IsBounded S₂ → ¬ Bornology.IsBounded (segments S₁ S₂)) ∧
      (¬ Bornology.IsBounded S₁ → S₂.Nonempty → ¬ Bornology.IsBounded (segments S₁ S₂)) ∧
      (Bornology.IsBounded S₁ → Bornology.IsBounded S₂ →
        Bornology.IsBounded (segments S₁ S₂)) := by -- --- PROOF ---
  -- `λ = 0` and `λ = 1` put each operand inside, given a point of the other
  have h₂ : S₁.Nonempty → S₂ ⊆ segments S₁ S₂ := fun ⟨y, hy⟩ x hx =>
    ⟨y, hy, x, hx, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  have h₁ : S₂.Nonempty → S₁ ⊆ segments S₁ S₂ := fun ⟨y, hy⟩ x hx =>
    ⟨x, hx, y, hy, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  refine ⟨fun h => Set.eq_empty_of_forall_notMem fun x ⟨y₁, hy₁, y₂, hy₂, _⟩ => ?_,
    fun ha hb => ha.mono (h₁ hb), fun ha hb => hb.mono (interior_mono (h₂ ha)),
    fun ha hb => ha.mono (interior_mono (h₁ hb)), fun ha hb hs => hb (hs.subset (h₂ ha)),
    fun ha hb hs => ha (hs.subset (h₁ hb)), fun ha hb => ?_⟩
  · rcases h with rfl | rfl
    · exact hy₁
    · exact hy₂
  -- inside the convex hull of the union, which is bounded
  · refine (isBounded_convexHull.mpr (ha.union hb)).subset ?_
    rintro x ⟨y₁, hy₁, y₂, hy₂, lam, ⟨hl₀, hl₁⟩, rfl⟩
    exact convex_convexHull ℝ (S₁ ∪ S₂) (subset_convexHull ℝ (S₁ ∪ S₂) (Or.inl hy₁))
      (subset_convexHull ℝ (S₁ ∪ S₂) (Or.inr hy₂)) hl₀ (sub_nonneg.mpr hl₁) (by ring)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
