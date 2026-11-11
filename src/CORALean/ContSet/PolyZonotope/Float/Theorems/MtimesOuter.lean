module

public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MulVecSplit

@[expose] public section

/-!
# `PolyZonotope.mtimes` over-approximates the image under a linear map

`InflatedContSet.map_subset` splits this into the nominal part and the box. The box is easy:
the old one travels through the map by `Interval.mtimes_outer`, and the spill is added on. The
nominal obligation is where the float layer pays for arithmetic: the center is wrong by a fixed
vector, which `residual` holds; each generator block is wrong by an entrywise amount its
coefficients scale, which `generatorError` sums. `mulVec_split` is stated at an arbitrary
coefficient vector, the regrouping being linear algebra; it takes the three blocks loose.

## Inputs
* `M` – matrix
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the matrix image of the set lies in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The image of a nominal point is a nominal point of the stored image, less the residual. -/
private theorem PolyZonotope.aux_mtimes_nominal (M : Mat 𝕋 m n)
    (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (toRealMat M *ᵥ ·) '' nominalSet pZ ⊆
      nominalSet (PolyZonotope.mtimes M pZ)
        + (PolyZonotope.mtimesResidual M pZ).toSet := by -- --- PROOF ---
  rintro _ ⟨x, hx', rfl⟩
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx'
  obtain ⟨r, hr, hxr⟩ := PolyZonotope.mtimes_point M pZ ha hβ hx
  exact ⟨_, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩, r, hr,
    funext fun i => (hxr i).symm⟩

/-- The old box travels through the map as a box, and the spill is added on. -/
private theorem PolyZonotope.aux_mtimes_error (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' (I_error pZ).toSet + (PolyZonotope.mtimesResidual M pZ).toSet ⊆
      (I_error (PolyZonotope.mtimes M pZ)).toSet :=
  subset_trans (Set.add_subset_add_right (Interval.mtimes_outer M pZ.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mtimes_outer (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (toRealMat M *ᵥ ·) '' pZ.toSet ⊆ (PolyZonotope.mtimes M pZ).toSet :=
  map_subset (fun x y => Matrix.mulVec_add _ x y)
    (PolyZonotope.aux_mtimes_nominal M pZ) (PolyZonotope.aux_mtimes_error M pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
