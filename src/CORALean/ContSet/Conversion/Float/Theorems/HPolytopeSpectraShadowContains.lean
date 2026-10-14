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

theorem HPolytope.spectraShadow_contains (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    P.construct ⊆ P.spectraShadow.construct := by -- --- PROOF ---
  intro x hx
  -- the error box is the origin, so the nominal part carries the point
  refine ⟨x, SpectraShadow.mem_nominalSet_iff.mpr ⟨x, HPolytope.posSemidef_spectraShadow P hx,
    fun i => ?_⟩, 0, ?_, add_zero x⟩
  · simp [HPolytope.spectraShadow, apply_ite (toReal : 𝕋 → ℝ), toReal_zero, toReal_one,
    Finset.sum_ite_eq]
  · -- the origin is the point `zero`
    have h0 : (0 : Vec ℝ n) = toRealVec (fun _ => (zero : 𝕋)) := funext fun i => toReal_zero.symm
    rw [h0]
    exact Interval.mem_point _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
