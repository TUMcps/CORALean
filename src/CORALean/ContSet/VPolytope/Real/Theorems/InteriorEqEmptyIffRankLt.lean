module

public import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# Degeneracy of a V-polytope, by a rank

[1, Eq. 17]: `⟨[v₁ … vₘ]⟩` is degenerate exactly when the points shifted by their mean,
`[v₁ - v̄ … vₘ - v̄]`, have rank below `n`. Their columns span the direction of the affine hull,
the pairwise differences being differences of shifted points and each shifted point the mean of
differences. At least one point, so that the mean exists.

## Inputs
* `P` – polytope

## Hypotheses
* `hk` – `P` has a vertex

## Conclusion
* the interior is empty iff the centered vertex matrix has rank below `n`

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

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.interior_eq_empty_iff_rank_lt (P : VPolytope (Vec ℝ n))
    (hk : 0 < P.k) : -- --- CONCL ---
    interior P.construct = ∅ ↔
      (Matrix.of fun i l => P.V l i - (∑ m, P.V m i) / P.k :
        Mat ℝ n P.k).rank < n := by -- --- PROOF ---
  set vbar : Vec ℝ n := fun i => (∑ m, P.V m i) / P.k with hvbar
  have hcol : (Matrix.of fun i l => P.V l i - (∑ m, P.V m i) / P.k : Mat ℝ n P.k).col =
      fun l => P.V l - vbar := rfl
  -- the shifted points span the direction of the affine hull
  have hspan : Submodule.span ℝ (Set.range fun l => P.V l - vbar) =
      vectorSpan ℝ (Set.range P.V) := by
    apply le_antisymm
    -- each shifted point is the mean of differences of points
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      have hk' : (P.k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      -- `vᵢ - v̄ = (1/k) ∑ₘ (vᵢ - vₘ)`
      have hsh : P.V l - vbar = (P.k : ℝ)⁻¹ • ∑ m, (P.V l - P.V m) := by
        funext i
        simp only [hvbar, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
      show P.V l - vbar ∈ _
      rw [hsh]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m _ =>
        vsub_mem_vectorSpan ℝ (Set.mem_range_self l) (Set.mem_range_self m))
    · rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
      have : P.V l -ᵥ P.V m = (P.V l - vbar) - (P.V m - vbar) := by
        rw [vsub_eq_sub]
        abel
      show P.V l -ᵥ P.V m ∈ _
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨l, rfl⟩)
        (Submodule.subset_span ⟨m, rfl⟩)
  -- full-dimensional iff the shifted points span `ℝⁿ` iff their rank is `n`
  have hne : (Set.range P.V).Nonempty := ⟨P.V ⟨0, hk⟩, Set.mem_range_self _⟩
  have hle := Matrix.rank_le_height (Matrix.of fun i l => P.V l i - (∑ m, P.V m i) / P.k :
    Mat ℝ n P.k)
  rw [← Set.not_nonempty_iff_eq_empty, VPolytope.isFullDim_iff,
    AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne, ← hspan,
    Matrix.rank_eq_finrank_span_cols, hcol]
  constructor
  · intro h
    refine lt_of_le_of_ne ?_ fun heq => h (Submodule.eq_top_of_finrank_eq ?_)
    · rw [Matrix.rank_eq_finrank_span_cols, hcol] at hle
      exact hle
    · rw [heq, Module.finrank_fin_fun]
  · intro h htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h
    exact lt_irrefl _ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
