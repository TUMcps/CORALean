module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# What a linear map does to emptiness, degeneracy and boundedness

[1, Table 1 (MS)]: an invertible `M` keeps every property of `S`; a singular one keeps
emptiness and boundedness and makes every image degenerate, its range being a proper subspace;
what it does to an unbounded set is left open, rightly — a projection can make it bounded.

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

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem image_linearMap_properties (M : Vec ℝ n →ₗ[ℝ] Vec ℝ n) (S : Set (Vec ℝ n)) :
    (S = ∅ → M '' S = ∅) ∧ (S.Nonempty → (M '' S).Nonempty) ∧
      (Bornology.IsBounded S → Bornology.IsBounded (M '' S)) ∧
      (Function.Bijective M →
        (interior S = ∅ → interior (M '' S) = ∅) ∧
        ((interior S).Nonempty → (interior (M '' S)).Nonempty) ∧
        (¬ Bornology.IsBounded S → ¬ Bornology.IsBounded (M '' S))) ∧
      (¬ Function.Bijective M → interior (M '' S) = ∅) := by -- --- PROOF ---
  refine ⟨fun h => by rw [h, Set.image_empty], fun h => h.image M, fun h => ?_, fun hM => ?_,
    fun hM => ?_⟩
  -- a linear map on `ℝⁿ` is Lipschitz
  · exact (LinearMap.toContinuousLinearMap M).lipschitz.isBounded_image h
  -- invertible: a homeomorphism, which carries interiors, with a Lipschitz inverse
  · let e := (LinearEquiv.ofBijective M hM).toContinuousLinearEquiv
    have he : ∀ T : Set (Vec ℝ n), M '' T = e '' T := fun T => rfl
    have hint : interior (M '' S) = M '' interior S := by
      rw [he, he]
      exact (e.toHomeomorph.image_interior S).symm
    refine ⟨fun h => by rw [hint, h, Set.image_empty], fun h => by rw [hint]; exact h.image M,
      fun hS hb => hS ?_⟩
    have hS : S = e.symm '' (M '' S) := by
      rw [he, ← Set.image_comp]
      simp
    rw [hS]
    exact (e.symm : Vec ℝ n →L[ℝ] Vec ℝ n).lipschitz.isBounded_image hb
  -- singular: the image lies in the range, a proper subspace, which has no interior
  · by_contra hne
    have hsub : interior (M '' S) ⊆ interior (LinearMap.range M : Set (Vec ℝ n)) :=
      interior_mono (Set.image_subset_range M S)
    have htop := Submodule.eq_top_of_nonempty_interior' (LinearMap.range M)
      ((Set.nonempty_iff_ne_empty.mpr hne).mono hsub)
    have hsurj : Function.Surjective M := LinearMap.range_eq_top.mp htop
    exact hM ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
