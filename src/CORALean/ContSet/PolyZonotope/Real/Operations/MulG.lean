import CORALean.Global.Hadamard
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinG

/-!
# The generators of `mul`

`bilinG` at the entrywise product. Which bilinear map is paired is the only
thing that separates a coordinatewise product from a matrix one, so `mul` is
`bilin` at `hadamardLin` and this is where that choice is made.

`hadamardLin_vec` is what keeps the statements downstream reading as `*`: at
`Vec` a coordinate is an application, so the bundled product is the `Pi` one
definitionally.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the product: the two extended generators, multiplied
coordinate by coordinate. -/
def PolyZonotope.mulG (S₁ S₂ : PolyZonotope (Vec ℝ n)) :
    Fin ((S₁.h + 1) * (S₂.h + 1)) → Vec ℝ n :=
  PolyZonotope.bilinG Entrywise.hadamardLin S₁ S₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
