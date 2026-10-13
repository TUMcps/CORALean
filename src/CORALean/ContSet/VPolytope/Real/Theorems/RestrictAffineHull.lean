module

public import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
public import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# A degenerate V-polytope, restricted to its affine hull

[1, Sec. 4.1 (V affine hull)]: let the first `r` columns of an orthogonal `U` span the direction
of the affine hull of `P = ⟨[v₁ … vₘ]⟩` — what the singular value decomposition of a basis `B =
U Σ Vᵀ` of that direction gives — and `c` lie in the hull. With `M = [I_r 0] Uᵀ`, the polytope
`P' = ⟨[M(v₁ - c) … M(vₘ - c)]⟩ ⊂ ℝʳ` is non-degenerate and `P = Mᵀ P' + c`: `MᵀM` is the
orthogonal projection onto those columns, which fixes every `x - c`, and `M` carries the
direction of the hull onto all of `ℝʳ`. The decomposition itself is a hypothesis.

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

variable {n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.restrict_affineHull (P : VPolytope (Vec ℝ n)) (c : Vec ℝ n) (U : Mat ℝ n n)
    (hU : Uᵀ * U = 1) (hrn : r ≤ n) (hc : c ∈ affineSpan ℝ (Set.range P.V))
    (hspan : Submodule.span ℝ (Set.range fun j : Fin r => U.col (Fin.castLE hrn j)) =
      vectorSpan ℝ (Set.range P.V)) :
    let M : Mat ℝ r n := Matrix.of fun i l => U l (Fin.castLE hrn i)
    let P' : VPolytope (Vec ℝ r) := ⟨P.k, fun i => M *ᵥ (P.V i - c)⟩
    P.construct = (fun y => Mᵀ *ᵥ y + c) '' P'.construct ∧
      (interior P'.construct).Nonempty := by -- --- PROOF ---
  intro M P'
  -- `M` sends the first `r` columns of `U` to the unit vectors, and `Mᵀ` sends them back
  have hMu : ∀ j : Fin r, M *ᵥ U.col (Fin.castLE hrn j) = Pi.single j 1 := fun j => by
    funext i
    have := congrFun (congrFun hU (Fin.castLE hrn i)) (Fin.castLE hrn j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.col, Matrix.transpose_apply,
      Pi.single_apply]
    rw [this]
    simp [Fin.castLE_inj]
  have hMt : ∀ j : Fin r, Mᵀ *ᵥ Pi.single j 1 = U.col (Fin.castLE hrn j) := fun j => by
    funext l
    simp [M, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.col]
  -- so `MᵀM` fixes the span of those columns, which is the direction of the hull
  have hfix : ∀ w ∈ vectorSpan ℝ (Set.range P.V), Mᵀ *ᵥ (M *ᵥ w) = w := by
    rw [← hspan]
    intro w hw
    have hker : Submodule.span ℝ (Set.range fun j : Fin r => U.col (Fin.castLE hrn j)) ≤
        LinearMap.ker (Matrix.mulVecLin (Mᵀ * M) - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.id_apply]
      rw [← Matrix.mulVec_mulVec, hMu, hMt, sub_self]
    have := hker hw
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
      LinearMap.id_apply, sub_eq_zero] at this
    rw [Matrix.mulVec_mulVec]
    exact this
  -- `P'` is the image of `P` under `x ↦ M (x - c)`
  have hP' : P'.construct = (fun x => M *ᵥ (x - c)) '' P.construct := by
    rw [VPolytope.construct_eq_convexHull, VPolytope.construct_eq_convexHull]
    let f : Vec ℝ n →ᵃ[ℝ] Vec ℝ r := ⟨fun x => M *ᵥ (x - c), Matrix.mulVecLin M, fun p v => by
      simp [Matrix.mulVec_add, Matrix.mulVec_sub, vadd_eq_add]
      abel⟩
    have hf : (fun x => M *ᵥ (x - c)) = f := rfl
    rw [hf, f.image_convexHull, ← Set.range_comp]
    rfl
  have hmemdir : ∀ x ∈ P.construct, x - c ∈ vectorSpan ℝ (Set.range P.V) := fun x hx => by
    rw [P.construct_eq_convexHull] at hx
    have hxa : x ∈ affineSpan ℝ (Set.range P.V) :=
      (convexHull_subset_affineSpan _) hx
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hxa hc
  -- `MᵀM (x - c) + c = x` on `P`
  refine ⟨?_, ?_⟩
  · rw [hP', ← Set.image_comp]
    ext x
    constructor
    · intro hx
      refine ⟨x, hx, ?_⟩
      show Mᵀ *ᵥ (M *ᵥ (x - c)) + c = x
      rw [hfix _ (hmemdir x hx), sub_add_cancel]
    · rintro ⟨y, hy, rfl⟩
      show Mᵀ *ᵥ (M *ᵥ (y - c)) + c ∈ P.construct
      rw [hfix _ (hmemdir y hy), sub_add_cancel]
      exact hy
  -- `M` maps the direction of the hull onto `ℝʳ`
  · rw [VPolytope.isFullDim_iff]
    have hne : (Set.range P'.V).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hk : P.k = 0 := by
        by_contra hk
        exact (Set.range_eq_empty_iff.mp hemp).false ⟨0, Nat.pos_of_ne_zero hk⟩
      have hr0 : Set.range P.V = ∅ := by
        rw [Set.range_eq_empty_iff]
        exact ⟨fun i => absurd i.2 (by omega)⟩
      rw [hr0, AffineSubspace.span_empty] at hc
      exact hc
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne,
      eq_top_iff]
    rintro w -
    -- `w = M (∑ wⱼ uⱼ)`, and `∑ wⱼ uⱼ` is a difference of points of the hull's direction
    have hw : w = M *ᵥ ∑ j : Fin r, w j • U.col (Fin.castLE hrn j) := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hMu]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have hdir : ∑ j : Fin r, w j • U.col (Fin.castLE hrn j) ∈ vectorSpan ℝ (Set.range P.V) := by
      rw [← hspan]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [hw]
    -- the image of the hull's direction is the direction of `P'`'s points
    have hle : (vectorSpan ℝ (Set.range P.V)).map (Matrix.mulVecLin M) ≤
        vectorSpan ℝ (Set.range P'.V) := by
      rw [vectorSpan_def, Submodule.map_span, vectorSpan_def, Submodule.span_le]
      rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, ?_⟩
      simp [P', vsub_eq_sub, Matrix.mulVec_sub]
    exact hle ⟨_, hdir, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
