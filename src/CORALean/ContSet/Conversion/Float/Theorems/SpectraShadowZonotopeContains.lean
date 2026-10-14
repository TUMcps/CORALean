module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.SpectraShadowIntervalContains
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemBase
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# A spectrahedral shadow as a zonotope, over a floating-point scalar

CORA's `zonotope(SpS)`: `G Z + c`, `Z` the interval hull of the base spectrahedron as a
zonotope. The hull is the certified one (`SpectraShadow.interval` of `SpectraShadow.base`, the
`2m` dual certificates the caller's), the image by `G` the float `Zonotope.mtimes`, and the
centre with the error box a box added by `Zonotope.plus`. `none` when a certificate fails. An
enclosure, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.zonotope_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k} {Z : Zonotope (Vec 𝕋 n)} (h : S.zonotope Yup Ylo = some Z) :
    S.construct ⊆ Z.construct := by -- --- PROOF ---
  simp only [SpectraShadow.zonotope, Option.map_eq_some_iff] at h
  obtain ⟨B, hB, rfl⟩ := h
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨β, hP, hyβ⟩ := SpectraShadow.mem_nominalSet_iff.mp hy
  -- `β` is in the certified box, so `G β` in the image zonotope
  have hβ := (Interval.zonotope_contains B) (SpectraShadow.interval_contains hB
    (SpectraShadow.mem_base hP))
  have hGβ := Zonotope.mtimes_outer (fun r j => S.G j r) B.zonotope ⟨β, hβ, rfl⟩
  -- the centre plus the error is in the box zonotope
  have hce : toRealVec S.c + e ∈ ((Interval.point S.c).plus S.I_error).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.plus_outer _ _ ⟨_, Interval.mem_point S.c, e, he, rfl⟩)
  refine Zonotope.plus_outer _ _ ⟨_, hGβ, _, hce, ?_⟩
  funext r
  simp only [Pi.add_apply, hyβ r, Matrix.mulVec, dotProduct, toRealMat, toRealVec]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
