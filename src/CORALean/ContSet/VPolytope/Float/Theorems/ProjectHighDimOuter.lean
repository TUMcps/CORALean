module

public import CORALean.ContSet.VPolytope.Float.Operations.ProjectHighDim
public import CORALean.ContSet.VPolytope.Real.Theorems.ProjectHighDimExact
public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.Interval.Float.Theorems.ProjectHighDimOuter

@[expose] public section

/-!
# `VPolytope.projectHighDim` over-approximates the padded image

The padded vertices are the exact layer's image of the nominal vertices under the padding map,
so the nominal part is `projectHighDim_exact`; the error box is `Interval.projectHighDim_outer`.
Outer, as the box's emptiness test is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.projectHighDim_outer (P : VPolytope (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) :
    (fun x => Function.extend dims x 0) '' P.construct ⊆
      (P.projectHighDim dims).construct := by -- --- PROOF ---
  -- padding with zeros is the padding matrix, vertex by vertex
  have hmat : ∀ x : Vec ℝ n, Function.extend dims x 0 =
      (Matrix.of fun (i : Fin N) (k : Fin n) => if dims k = i then (1 : ℝ) else 0) *ᵥ x := by
    intro x
    funext j
    by_cases h : ∃ k, dims k = j
    · obtain ⟨k, rfl⟩ := h
      simp [Matrix.mulVec, dotProduct, hdims.extend_apply, hdims.eq_iff]
    · rw [Function.extend_apply' _ _ _ h]
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      have : dims k ≠ j := fun hk => h ⟨k, hk⟩
      simp [this]
  refine image_subset (fun _ _ => ?_) ?_ (Interval.projectHighDim_outer P.E dims hdims)
  · rw [hmat, hmat, hmat, Matrix.mulVec_add]
  · -- the nominal vertices of the result are the padded nominal vertices
    have hnom : nominal (P.projectHighDim dims) =
        Real.VPolytope.projectHighDim (nominal P) dims := by
      show (⟨P.k, _⟩ : CORALean.Real.VPolytope (Vec ℝ N)) = ⟨P.k, _⟩
      congr 1
      funext l j
      change toReal ((P.projectHighDim dims).V l j) = _
      by_cases h : ∃ k, dims k = j
      · -- a coordinate in the range of `dims` reads the vertex's entry
        obtain ⟨k, rfl⟩ := h
        have hf : Fin.find (fun k' => dims k' = dims k) ⟨k, rfl⟩ = k :=
          hdims (Fin.find_spec (p := fun k' => dims k' = dims k) ⟨k, rfl⟩)
        simp only [VPolytope.projectHighDim, dif_pos (⟨k, rfl⟩ : ∃ k', dims k' = dims k), hf]
        simp [Matrix.mulVec, dotProduct, hdims.eq_iff]
        rfl
      · -- any other coordinate is `0` on both sides
        simp only [VPolytope.projectHighDim, dif_neg h, toReal_zero]
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
        refine (Finset.sum_eq_zero fun k _ => ?_).symm
        have : dims k ≠ j := fun hk => h ⟨k, hk⟩
        simp [this]
    show _ '' ContSet.construct (nominal P) ⊆ ContSet.construct (nominal (P.projectHighDim dims))
    rw [hnom]
    have hex := Real.VPolytope.projectHighDim_exact (nominal P) dims
    rintro _ ⟨x, hx, rfl⟩
    have hm : (Matrix.of fun (i : Fin N) (k : Fin n) => if dims k = i then (1 : ℝ) else 0) *ᵥ x ∈
        Real.VPolytope.construct ((nominal P).projectHighDim dims) := by
      rw [hex]; exact ⟨x, hx, rfl⟩
    show Function.extend dims x 0 ∈ ContSet.construct _
    rw [hmat]
    exact hm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
