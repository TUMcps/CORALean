module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Theorems.BilinRefines
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact

@[expose] public section

/-!
# `PolyZonotope.quadMap` over-approximates the image under a quadratic map

The exact layer proves the hard half — that the image of a polynomial zonotope
under a quadratic map *is* a polynomial zonotope — and this file adds only what
rounding costs. `absorbRounding` runs first and leaves a set with no independent
block and no error box, so `quadMapDep_exact` applies to the nominal part as it
stands; from there the two representations differ in their generator entries
alone, and `generatorError` prices that difference exactly as it does for
`mtimes`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the whole operation: `absorbRounding` first, then the exact map, then this refinement
theorem PolyZonotope.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' pZ.construct
      ⊆ (PolyZonotope.quadMap Q pZ).construct := by
  refine subset_trans (Set.image_mono (PolyZonotope.absorbRounding_nominal pZ)) ?_
  refine subset_trans ?_ (PolyZonotope.bilin_refines Q pZ.absorbRounding pZ.absorbRounding rfl)
  exact (Real.PolyZonotope.quadMapDep_exact (fun k => toRealMat (Q k))
    (nominal pZ.absorbRounding) rfl).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
