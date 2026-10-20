module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.SpectraShadow.Float.Operations.PadLeft
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
public import CORALean.Global.Block

@[expose] public section

/-!
# `SpectraShadow.padLeft` contains the embedded shadow

Padding rounds nothing, so `InflatedContSet.image_subset` splits this into the nominal shadow and
the box. The nominal shadow of the padded one is the exact layer's `map` of the nominal
shadow under `blockPadLeft`, so `map_exact` gives the nominal obligation as an equality; the
box's new coordinates are the exact zeros `padLeft` stores.

## Inputs
* `S` – spectrahedral shadow
* `m` – natural number

## Hypotheses
* none

## Conclusion
* `SpectraShadow.padLeft` contains the embedded shadow
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
theorem SpectraShadow.aux_padLeft_nominal (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    nominal (S.padLeft m) = (nominal S).map (blockPadLeft n m) := by -- --- PROOF ---
  show Real.SpectraShadow.mk _ _ _ _ _ _ = Real.SpectraShadow.mk _ _ _ _ _ _
  congr 1
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec]
      rfl
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec, toReal_zero]
  · funext j
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec]
      rfl
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec, toReal_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.padLeft_outer (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (m : ℕ) :
    ⇑(blockPadLeft n m) '' S.construct ⊆ (S.padLeft m).construct :=
  image_subset (fun _ _ => map_add _ _ _)
    (by
      show ⇑(blockPadLeft n m) '' nominalSet S ⊆ ContSet.construct (nominal (S.padLeft m))
      rw [SpectraShadow.aux_padLeft_nominal]
      exact le_of_eq (Real.SpectraShadow.map_exact _ _))
    (by
      rintro _ ⟨e, he, rfl⟩ i
      show toReal ((Fin.append S.I_error.inf fun _ => zero) i) ≤ (Fin.append e 0) i
        ∧ (Fin.append e 0) i ≤ toReal ((Fin.append S.I_error.sup fun _ => zero) i)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h : toReal (S.I_error.inf j) ≤ e j ∧ e j ≤ toReal (S.I_error.sup j) := he j
        simpa using h
      · simp [toReal_zero])


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
