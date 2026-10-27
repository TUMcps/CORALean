module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-!
# What the convex hull does to emptiness, degeneracy and boundedness

[1, Table 1 (conv)] with `conv(S₁, S₂) = {λ s₁ + (1 - λ) s₂}` [1, Table 3], which is
`Set.linComb`: empty if either operand is; with both nonempty it contains both, so it inherits an
interior and unboundedness from either; bounded operands give a bounded hull. The table also
claims "D conv ND = ND", "D conv NB = NB", "ND conv B = ND" and "B conv NB = NB", which fail at
an empty operand — degenerate and bounded in the paper's convention, and absorbing under this
`conv` (`setLinComb_properties_counterexample`).

## Inputs
* `S₁` – first set
* `S₂` – second set

## Hypotheses
* none

## Conclusion
* emptiness, interior and boundedness of the linear combination follow from the operands

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem setLinComb_properties (S₁ S₂ : Set (Vec ℝ n)) : -- --- CONCL ---
    (S₁ = ∅ ∨ S₂ = ∅ → Set.linComb S₁ S₂ = ∅) ∧
      (S₁.Nonempty → S₂.Nonempty → (Set.linComb S₁ S₂).Nonempty) ∧
      (S₁.Nonempty → (interior S₂).Nonempty → (interior (Set.linComb S₁ S₂)).Nonempty) ∧
      ((interior S₁).Nonempty → S₂.Nonempty → (interior (Set.linComb S₁ S₂)).Nonempty) ∧
      (S₁.Nonempty → ¬ Bornology.IsBounded S₂ → ¬ Bornology.IsBounded (Set.linComb S₁ S₂)) ∧
      (¬ Bornology.IsBounded S₁ → S₂.Nonempty → ¬ Bornology.IsBounded (Set.linComb S₁ S₂)) ∧
      (Bornology.IsBounded S₁ → Bornology.IsBounded S₂ →
        Bornology.IsBounded (Set.linComb S₁ S₂)) := by -- --- PROOF ---
  -- `λ = 0` and `λ = 1` put each operand inside, given a point of the other
  have h₂ : S₁.Nonempty → S₂ ⊆ Set.linComb S₁ S₂ := fun ⟨y, hy⟩ x hx =>
    ⟨y, hy, x, hx, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  have h₁ : S₂.Nonempty → S₁ ⊆ Set.linComb S₁ S₂ := fun ⟨y, hy⟩ x hx =>
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
