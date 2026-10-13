import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
import CORALean.ContSet.Interval.Float.Theorems.ProjectHighDimOuter
import CORALean.ContSet.Zonotope.Float.Operations.ProjectHighDim
import CORALean.ContSet.Zonotope.Real.Theorems.ProjectHighDimExact

/-!
# `Zonotope.projectHighDim_` over-approximates the zero-padded set

Padding is linear and rounds nothing, so `InflatedContSet.image_subset` splits this into the
nominal zonotope and the box. For injective `proj` the exact layer's padding map `embed` is
`Function.extend proj · 0`, and the nominal zonotope of the result is the exact layer's
`projectHighDim_` of the nominal one, so `Zonotope.map_exact` gives the nominal obligation as an
equality; the box is `Interval.projectHighDim_outer`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact padding map reads the first (only) preimage, as `projectHighDim_` does. -/
theorem Zonotope.aux_embed_find (proj : Fin n → Fin N) (hproj : Function.Injective proj)
    (y : Vec ℝ n) (j : Fin N) :
    Real.Zonotope.embed proj y j = if h : ∃ k, proj k = j then
      y (Fin.find (fun k => proj k = j) h) else 0 := by -- --- PROOF ---
  classical
  simp only [Real.Zonotope.embed, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  by_cases h : ∃ k, proj k = j
  · rw [dif_pos h, Finset.sum_eq_single (Fin.find (fun k => proj k = j) h)]
    · rw [if_pos (Fin.find_spec (p := fun k => proj k = j) h), one_mul]
    · intro k _ hk
      rw [if_neg, zero_mul]
      intro hkj
      exact hk (hproj (hkj.trans (Fin.find_spec (p := fun k => proj k = j) h).symm))
    · simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg fun hk => h ⟨k, hk⟩, zero_mul]

theorem Zonotope.aux_nominal_projectHighDim_ (Z : Zonotope (Vec 𝕋 n)) (proj : Fin n → Fin N)
    (hproj : Function.Injective proj) :
    nominal (Z.projectHighDim_ N proj)
      = Real.Zonotope.projectHighDim_ (nominal Z) proj := by -- --- PROOF ---
  show Real.Zonotope.mk _ _ _ = Real.Zonotope.mk _ _ _
  congr 1
  · funext j
    rw [Zonotope.aux_embed_find proj hproj]
    show toReal (if h : ∃ k, proj k = j then _ else _) = _
    by_cases h : ∃ k, proj k = j
    · rw [dif_pos h, dif_pos h]; rfl
    · rw [dif_neg h, dif_neg h, toReal_zero]
  · funext l j
    show toReal ((Z.projectHighDim_ N proj).G l j) = Real.Zonotope.embed proj _ j
    rw [Zonotope.aux_embed_find proj hproj]
    show toReal (if h : ∃ k, proj k = j then _ else _) = _
    by_cases h : ∃ k, proj k = j
    · rw [dif_pos h, dif_pos h]; rfl
    · rw [dif_neg h, dif_neg h, toReal_zero]

/-- Padding reads as the exact layer's `embed`. -/
theorem Zonotope.aux_extend_eq_embed (proj : Fin n → Fin N) (hproj : Function.Injective proj)
    (y : Vec ℝ n) : Function.extend proj y 0 = Real.Zonotope.embed proj y := by -- --- PROOF ---
  funext j
  rw [Zonotope.aux_embed_find proj hproj]
  by_cases h : ∃ k, proj k = j
  · rw [dif_pos h]
    have hs := Fin.find_spec (p := fun k => proj k = j) h
    calc Function.extend proj y 0 j
        = Function.extend proj y 0 (proj (Fin.find (fun k => proj k = j) h)) := by rw [hs]
      _ = _ := hproj.extend_apply _ _ _
  · rw [dif_neg h, Function.extend_apply' _ _ _ h]; rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.projectHighDim_outer (Z : Zonotope (Vec 𝕋 n)) (proj : Fin n → Fin N)
    (hproj : Function.Injective proj) :
    (fun x => Function.extend proj x 0) '' Z.construct ⊆
      (Z.projectHighDim_ N proj).construct := by -- --- PROOF ---
  have hext : (fun x : Vec ℝ n => Function.extend proj x 0) = Real.Zonotope.embed proj :=
    funext (Zonotope.aux_extend_eq_embed proj hproj)
  refine image_subset (fun x y => by simp only [congrFun hext]; exact map_add _ x y) ?_
    (Interval.projectHighDim_outer Z.E proj hproj)
  rw [hext]
  have h := Real.Zonotope.map_exact (Real.Zonotope.embed proj) (nominal Z)
  rw [← Real.Zonotope.projectHighDim_, ← Zonotope.aux_nominal_projectHighDim_ Z proj hproj] at h
  exact h.le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
