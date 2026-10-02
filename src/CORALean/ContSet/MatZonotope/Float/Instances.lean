import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.MatZonotope.Float.MatZonotope

/-!
# Float matrix zonotopes: the instances

What one denotes, `nominal + E`, as a `ContSet` over `Mat ℝ m n`: the reading a family of
system matrices needs, `LinParamSys` and `LinParamSysDT` asking for nothing else of it.
Its action on a float zonotope is `Mtimes`, declared with `Zonotope`'s own instances.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

instance {m n : ℕ} : ContSet (MatZonotope 𝕋 m n) (Mat ℝ m n) := ⟨MatZonotope.construct⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
