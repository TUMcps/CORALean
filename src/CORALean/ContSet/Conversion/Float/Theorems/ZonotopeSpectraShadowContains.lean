module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePosSemidefSpectraShadowIff
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeSpectraShadowExact
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePosSemidefSpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A zonotope as a spectrahedral shadow, over a floating-point scalar

`Zonotope.spectraShadow_contains`: its `spectraShadow` contains it.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope is contained in its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.spectraShadow_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.spectraShadow.construct := by -- --- PROOF ---
  -- the box is carried over, so only the nominal parts are compared
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hP, hx'⟩ := (Real.Zonotope.spectraShadow_exact (nominal Z)).subset hx
  change x = toRealVec Z.c
    + ∑ j : Fin Z.h, (β : Fin Z.h → ℝ) j • (fun i => toReal (Z.G j i) : Vec ℝ n) at hx'
  exact SpectraShadow.mem_nominalSet_iff.mpr
    ⟨β, Zonotope.posSemidef_spectraShadow Z β
      ((Real.Zonotope.posSemidef_spectraShadow_iff (nominal Z) β).mp hP),
      fun i => (congrFun hx' i).trans
      (Entrywise.add_sum_smul_apply (toRealVec Z.c) (fun j i => toReal (Z.G j i)) β i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
