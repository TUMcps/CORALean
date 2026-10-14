module

public import CORALean.ContSet.ContSet.Operations.Enclose
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `enclose` encloses the segments from `S` to `M S + S₂`

`mtimes_outer`, `plus_outer` and `linComb_outer` chained. The `linComb` is the convex hull of
the two operands where both are convex (`LinComb.convexHull_subset_linComb`), so for a convex
representation this contains CORA's hull; it is an enclosure, not an equality, for any
representation whose `linComb` is coarser than the hull.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Pointwise

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.enclose_outer (s : S n) (M : Mat 𝕋 n n) (s₂ : S n) :
    segments (construct s)
        ((fun y : Vec ℝ n => (toRealMat M).mulVec y) '' construct s + construct s₂) ⊆
      construct (ContSet.enclose s M s₂) := by -- --- PROOF ---
  have hm : (fun y : Vec ℝ n => (toRealMat M).mulVec y) '' construct s ⊆
      construct (Mtimes.mtimes M s) := by
    rintro _ ⟨y, hy, rfl⟩
    refine Mtimes.mtimes_outer (𝕄 := Mat 𝕋) M s ?_
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact ⟨y, hy, rfl⟩
  have hp : (fun y : Vec ℝ n => (toRealMat M).mulVec y) '' construct s + construct s₂ ⊆
      construct (Plus.plus (Mtimes.mtimes M s) s₂) :=
    (Set.add_subset_add hm subset_rfl).trans (Plus.plus_outer _ _)
  refine (?_ : segments (construct s) _ ⊆ segments (construct s) _).trans
    (LinComb.linComb_outer s _)
  rintro x ⟨y₁, h₁, y₂, h₂, lam, hl, rfl⟩
  exact ⟨y₁, h₁, y₂, hp h₂, lam, hl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
