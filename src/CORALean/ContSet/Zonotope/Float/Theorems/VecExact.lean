module

public import CORALean.ContSet.Zonotope.Float.Operations.Vec
public import CORALean.ContSet.Interval.Float.Theorems.VecExact
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# `Zonotope.vec` is exactly the stacked set

Stacking commutes with reading the floats as reals and is linear, so the nominal part follows the
exact layer's `vec_construct`, the error box `Interval.vec_exact`, and the image of the sum is the
sum of the images.

## Inputs
* `Z` – matrix zonotope

## Hypotheses
* none

## Conclusion
* the stacked zonotope denotes exactly the stackings of the members
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.vec_exact (Z : Zonotope (Mat 𝕋 m n)) : -- --- CONCL ---
    Z.vec.construct = matVecEquiv '' Z.construct := by -- --- PROOF ---
  -- the nominal part and the box are each exactly stacked
  have hn : nominalSet Z.vec = matVecEquiv '' nominalSet Z :=
    (Real.Zonotope.vec_construct Z.nominal).symm
  have hb : (I_error Z.vec).construct = matVecEquiv '' (I_error Z).construct :=
    Interval.vec_exact Z.I_error
  -- and the image of a Minkowski sum under an additive map is the sum of the images
  show nominalSet Z.vec + (I_error Z.vec).construct = _
  rw [hn, hb]
  exact (Set.image_add matVecEquiv.toLinearMap).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
