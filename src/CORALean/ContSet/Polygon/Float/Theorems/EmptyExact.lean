import CORALean.ContSet.Polygon.Float.Operations.Empty

/-!
# `Polygon.empty` is the empty set
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_empty :
    ContSet.construct (Polygon.empty 𝕋) = (∅ : Set (Vec ℝ 2)) := by
  ext x
  simp [SetUnion.mem_construct, Polygon.empty]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
