module

public import CORALean.ContSet.VPolytope.Float.Operations.Vec
public import CORALean.ContSet.Interval.Float.Theorems.VecExact
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `VPolytope.vec` is exactly the stacked set

Stacking commutes with reading the floats as reals and is linear, so the nominal hull follows the
exact layer's `vec_exact`, the error box `Interval.vec_exact`, and the image of the sum is the sum
of the images.

## Inputs
* `P` – matrix polytope

## Hypotheses
* none

## Conclusion
* the stacked polytope denotes exactly the stackings of the members
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

theorem VPolytope.vec_exact (P : VPolytope (Mat 𝕋 m n)) : -- --- CONCL ---
    InflatedContSet.construct P.vec =
      matVecEquiv '' InflatedContSet.construct P := by -- --- PROOF ---
  -- the nominal hull and the box are each exactly stacked
  have hn : nominalSet P.vec = matVecEquiv '' nominalSet P :=
    (Real.VPolytope.vec_exact P.nominal).symm
  have hb : (I_error P.vec).construct = matVecEquiv '' (I_error P).construct :=
    Interval.vec_exact P.I_error
  -- and the image of a Minkowski sum under an additive map is the sum of the images
  show nominalSet P.vec + (I_error P.vec).construct = _
  rw [hn, hb]
  exact (Set.image_add matVecEquiv.toLinearMap).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
