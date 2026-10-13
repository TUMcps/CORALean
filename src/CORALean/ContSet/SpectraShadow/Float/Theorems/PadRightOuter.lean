import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
import CORALean.ContSet.SpectraShadow.Float.Operations.PadRight
import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
import CORALean.Global.Block

/-!
# `SpectraShadow.padRight` contains the embedded shadow

Padding rounds nothing, so `InflatedContSet.image_subset` splits this into the nominal shadow and
the box. The nominal shadow of the padded one is the exact layer's `map` of the nominal
shadow under `blockPadRight`, so `map_exact` gives the nominal obligation as an equality; the
box's new coordinates are the exact zeros `padRight` stores.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The padded stored shadow reads as the nominal shadow mapped by the embedding. -/
theorem SpectraShadow.aux_padRight_nominal (S : SpectraShadow 𝕋 (Vec 𝕋 m)) :
    nominal (S.padRight n) = (nominal S).map (blockPadRight n m) := by -- --- PROOF ---
  show Real.SpectraShadow.mk _ _ _ _ _ _ = Real.SpectraShadow.mk _ _ _ _ _ _
  congr 1
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec, toReal_zero]
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec]
      rfl
  · funext j
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec, toReal_zero]
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec]
      rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.padRight_outer (n : ℕ) (S : SpectraShadow 𝕋 (Vec 𝕋 m)) :
    ⇑(blockPadRight n m) '' S.construct ⊆ (S.padRight n).construct :=
  image_subset (fun _ _ => map_add _ _ _)
    (by
      show ⇑(blockPadRight n m) '' nominalSet S ⊆ ContSet.construct (nominal (S.padRight n))
      rw [SpectraShadow.aux_padRight_nominal]
      exact le_of_eq (Real.SpectraShadow.map_exact _ _))
    (by
      rintro _ ⟨e, he, rfl⟩ i
      show toReal ((Fin.append (fun _ : Fin n => zero) S.E.inf) i) ≤ (Fin.append 0 e) i
        ∧ (Fin.append 0 e) i ≤ toReal ((Fin.append (fun _ : Fin n => zero) S.E.sup) i)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [toReal_zero]
      · have h : toReal (S.E.inf j) ≤ e j ∧ e j ≤ toReal (S.E.sup j) := he j
        simpa using h)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
