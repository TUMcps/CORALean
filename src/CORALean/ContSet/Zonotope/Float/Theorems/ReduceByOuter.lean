module

public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuterRefines

@[expose] public section

/-!
# `Zonotope.reduceBy` keeps the set it had

Nothing is argued twice: the exact layer already showed that boxing what a
partition drops over-approximates, and `reduceBy_outer_refines` that rounding the
block up only enlarges the result. Composing them gives the nominal inclusion,
and the box is untouched, hence `mono_subset`.

## Inputs
* `Z` – zonotope
* `part` – split into kept and reduced generators

## Hypotheses
* none

## Conclusion
* zonotope is contained in its reduction
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_reduceBy_nominal (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    nominalSet Z ⊆ nominalSet (Z.reduceBy part) :=
  subset_trans (Real.Zonotope.reduceBy_outer (nominal Z) part)
    (Zonotope.reduceBy_outer_refines Z part)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceBy_outer (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) :
    Z.construct ⊆ (Z.reduceBy part).construct :=
  mono_subset (Zonotope.aux_reduceBy_nominal Z part) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
