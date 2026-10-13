import CORALean.ContSet.Polygon.Float.Operations.Mldivide
import CORALean.ContSet.Polygon.Float.Theorems.SubtractOuter

/-!
# `Polygon.mldivide` encloses the difference with any set

When the converted polygon lies in `S`, the difference `P \ S` lies in `P \ Sp`, which
`Polygon.subtract_outer` takes into the result. Outer.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.mldivide_outer (P Sp : Polygon 𝕋) {S : Set (Vec ℝ 2)}
    (hSp : ContSet.construct Sp ⊆ S) :
    ContSet.construct P \ S ⊆ ContSet.construct (Polygon.mldivide P Sp) :=
  fun _ hx => Polygon.subtract_outer P Sp ⟨hx.1, fun h => hx.2 (hSp h)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
