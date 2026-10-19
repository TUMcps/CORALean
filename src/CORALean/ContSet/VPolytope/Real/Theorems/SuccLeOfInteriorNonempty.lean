module

public import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# A non-degenerate V-polytope needs `n + 1` points

[1, Sec. 4.2 fn. 3]'s dual half: a V-polytope in `ℝⁿ` with an interior point has at least
`n + 1` points, since `k` points span an affine subspace of dimension at most `k - 1`.

## Inputs
* `P` – polytope

## Hypotheses
* `h` – `P` has nonempty interior

## Conclusion
* `P` has at least `n + 1` vertices

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.succ_le_of_interior_nonempty (P : VPolytope (Vec ℝ n))
    (h : (interior P.construct).Nonempty) : n + 1 ≤ P.k := by -- --- PROOF ---
  have htop := (VPolytope.isFullDim_iff P).mp h
  obtain ⟨k, V⟩ := P
  cases k with
  -- no points: the span is `⊥`, which is not the whole space
  | zero =>
    have hr : Set.range V = ∅ := Set.range_eq_empty V
    rw [hr, AffineSubspace.span_empty] at htop
    exact absurd htop (AffineSubspace.bot_ne_top ℝ _ _)
  | succ m =>
    have hle := finrank_vectorSpan_range_le ℝ V (Fintype.card_fin (m + 1))
    rw [← direction_affineSpan, htop, AffineSubspace.direction_top, finrank_top,
      Module.finrank_fin_fun] at hle
    show n + 1 ≤ m + 1
    omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
