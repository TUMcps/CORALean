import CORALean.ContSet.Zonotope.Real.Operations.Map

/-!
# Zonotopes: multiplication by a single linear map

`map` at the one map a plain matrix denotes. What makes this an operation rather
than a use of `map` is that a caller holds *matrix data*, not a linear map, and
`LinMapSet` is what turns the one into the other — an abstract map is nothing an
algorithm could compute with.

At `Vec` this is `mtimes`. At `Mat` it is matrix multiplication of a matrix
zonotope, from either side, which is the same operation only because the
ambient type is a parameter.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

/-- `map` at a map read off `M`, which is sound whenever `M` denotes that one
map and no other. Its guarantee is `lmtimes_singleton_outer`. -/
def Zonotope.mapOf (f : α →ₗ[ℝ] β) (Z : Zonotope α) : Zonotope β := Z.map f

end CORALean.Real
