import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `randverify`: the system, held in a number type

`ẋ = A x + B u`, `y = C x` with `n = 5` states, 2 inputs and 2 outputs, `X0` as a zonotope (its
box, centre and diagonal generators) and `U` as a box, all read exactly, but for `X0` where
`x0Enclosed` says it encloses the file's box.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

structure RandSystem (𝕋 : Type) where
  A : Mat 𝕋 5 5
  B : Mat 𝕋 5 2
  C : Mat 𝕋 2 5
  X0 : Zonotope (Vec 𝕋 5)
  U : Interval (Vec 𝕋 2)
  dt : 𝕋
  /-- `X0`'s centre or radius was not a number of the format, so `X0` encloses the file's box. -/
  x0Enclosed : Bool := false

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
