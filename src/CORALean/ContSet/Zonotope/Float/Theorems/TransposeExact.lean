module

public import CORALean.ContSet.Zonotope.Float.Operations.Transpose
public import CORALean.ContSet.Interval.Float.Theorems.TransposeExact
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# `Zonotope.transpose` is exactly the transposed set

Transposition commutes with reading the floats as reals and is linear, so the nominal part follows
the exact layer's `transpose_exact`, the error box `Interval.transpose_exact`, and the image of
the sum is the sum of the images.

## Inputs
* `Z` – matrix zonotope

## Hypotheses
* none

## Conclusion
* the transposed zonotope denotes exactly the transposes of the members
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

theorem Zonotope.transpose_exact (Z : Zonotope (Mat 𝕋 m n)) : -- --- CONCL ---
    Z.transpose.construct = Matrix.transpose '' Z.construct := by -- --- PROOF ---
  -- the nominal part and the box are each exactly transposed
  have hn : nominalSet Z.transpose = Matrix.transpose '' nominalSet Z :=
    (Real.Zonotope.transpose_exact Z.nominal).symm
  have hb : (I_error Z.transpose).construct = Matrix.transpose '' (I_error Z).construct :=
    Interval.transpose_exact Z.I_error
  -- and the image of a Minkowski sum under an additive map is the sum of the images
  show nominalSet Z.transpose + (I_error Z.transpose).construct = _
  rw [hn, hb]
  exact (Set.image_add (Matrix.transposeLinearEquiv (Fin m) (Fin n) ℝ ℝ).toLinearMap).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
