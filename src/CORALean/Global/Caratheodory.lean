import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Carathéodory's theorem, over a fixed index

A point of the convex hull of `T` in a space of dimension `d` is a convex
combination of `d + 1` points of `T`, and so — padding the rest with weight
zero — of `a` of them for any `a` past that. Mathlib states the theorem as a
union over affinely independent finsets, a bound on the *cardinality* of a
subset. A closed-form set representation cannot index by a finset whose size
depends on the point: it needs one block of factors per summand, fixed in
advance, and `Fin a` is that.

Here rather than under `ContSet/`, because nothing in it names a representation
or a `construct` — it is a statement about a finite-dimensional real space, on
a par with `Global/Radstrom.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Module


-- =======================================  MAIN THEOREM  ======================================= --

/-- The convex hull of `T`, as the convex combinations of exactly `a` of its
points, for any `a` at least one past the dimension. -/
theorem convexHull_eq_fin {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {a : ℕ} (ha : finrank ℝ E + 1 ≤ a) (T : Set E) :
    convexHull ℝ T = {x | ∃ y : Fin a → E, ∃ lam : Fin a → ℝ, (∀ j, y j ∈ T)
      ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ x = ∑ j, lam j • y j} := by -- --- PROOF ---
  classical
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) ?_
  · -- Carathéodory, as an affinely independent family and its positive weights
    obtain ⟨ι, hι, z, w, hzs, hai, hwpos, hwsum, hwx⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hwsum
    -- affine independence is what bounds the family by the dimension
    have hcard : Fintype.card ι ≤ a :=
      le_trans (le_trans hai.card_le_finrank_succ
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)) ha
    obtain ⟨f⟩ : Nonempty (ι ↪ Fin a) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    have hg : ∀ i, Function.invFun (f : ι → Fin a) (f i) = i :=
      Function.leftInverse_invFun f.injective
    -- the padding: an index outside the embedding's range carries weight zero
    have hsum : ∀ {M : Type} [AddCommMonoid M] (F : Fin a → M),
        (∀ j, j ∉ Finset.univ.map f → F j = 0) → ∑ j, F j = ∑ i, F (f i) := by
      intro M _ F hF
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f)) (fun j _ hj => hF j hj),
        Finset.sum_map]
    refine ⟨fun j => z (Function.invFun (f : ι → Fin a) j),
      fun j => if j ∈ Finset.univ.map f then w (Function.invFun (f : ι → Fin a) j) else 0,
      fun j => hzs ⟨_, rfl⟩, fun j => by
        by_cases h : j ∈ Finset.univ.map f <;> simp [h, (hwpos _).le], ?_, ?_⟩
    · rw [hsum _ (fun j hj => if_neg hj), ← hwsum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [if_pos (Finset.mem_map_of_mem f (Finset.mem_univ i)), hg]
    · rw [hsum _ (fun j hj => by simp only [if_neg hj, zero_smul]), ← hwx]
      exact (Finset.sum_congr rfl fun i _ => by
        simp only [if_pos (Finset.mem_map_of_mem f (Finset.mem_univ i)), hg]).symm
  · -- the easy half: a convex set is closed under its own combinations
    rintro x ⟨y, lam, hy, hlam, hsum, rfl⟩
    exact Convex.sum_mem (convex_convexHull ℝ T) (fun j _ => hlam j) hsum
      (fun j _ => subset_convexHull ℝ T (hy j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
