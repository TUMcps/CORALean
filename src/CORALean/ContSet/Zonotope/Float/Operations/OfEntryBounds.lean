import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError

/-!
# `Zonotope.ofEntryBounds`

How an operation whose exact result is a zonotope with its own centre and generators —
a matrix zonotope's product with a zonotope is one — rounds it: floats either side of
each exact coordinate of the centre and of every generator, the lower ones stored. The
centre's gap is `residual`, the generators' is `generatorError` at their widths, and both
join the box `E` the operation already owes; the generator count is the exact one's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower bounds stored, the gaps to the upper ones paid into the box beside `E`. -/
def Zonotope.ofEntryBounds {h : ℕ} (cLo cHi : Vec 𝕋 n) (GLo GHi : Mat 𝕋 n h)
    (E : Interval (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let W : Mat 𝕋 n h := fun i k => subUp (GHi i k) (GLo i k)       -- each generator's width
  { h := h
    c := cLo
    G := fun k i => GLo i k
    E := (E.plus (Interval.residual cLo cHi cLo)).plus (Zonotope.generatorError W) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
