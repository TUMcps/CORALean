module

public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePosSemidefSpectraShadow
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopePosSemidefSpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A polytope as a spectrahedral shadow, over a floating-point scalar

`HPolytope.spectraShadow_contains`: its `spectraShadow` contains it.

## Inputs
* `P` – halfspace polytope

## Hypotheses
* none

## Conclusion
* polytope is contained in its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.spectraShadow_contains (P : HPolytope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    P.construct ⊆ P.spectraShadow.construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  -- the error box is the polytope's own, the nominal part carries the point
  refine ⟨y, SpectraShadow.mem_nominalSet_iff.mpr ⟨y, HPolytope.posSemidef_spectraShadow P hy,
    fun i => ?_⟩, e, he, rfl⟩
  simp [HPolytope.spectraShadow, apply_ite (toReal : 𝕋 → ℝ), toReal_zero, toReal_one,
    Finset.sum_ite_eq]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
