import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# `PolyZonotope.dependent`

Every free coefficient made dependent, by giving it a fresh factor that appears
in it alone and to the first power. The exact layer frees the independent
generators; here there is a second block of free coefficients — the error box —
and freeing it is the same construction, so this one operation does both and
leaves `q = 0` together with an empty box.

That is what `quadMap` needs. A quadratic map is not additive, so a nominal part
and a box cannot travel through it separately: `(x+e)ᵀQ(x+e)` is not
`xᵀQx + eᵀQe`, and the cross term has to be bounded against the whole set. Empty
the box first and the question does not arise.

Emptying it costs no rounding, which is why `errorBound` takes the larger
magnitude of the two endpoints rather than the box's midpoint and radius:
`maximum` and `absolute` are exact, where a midpoint would have to be stored as
a float and leave a residual behind. The price is a generator up to twice as
wide on an off-centre coordinate, which for a box of rounding error is nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.dependent (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := PZ.p + (PZ.q + n)
  h := PZ.h + (PZ.q + n)
  q := 0
  c := PZ.c
  G := fun i => Fin.append (PZ.G i)
    (Fin.append (PZ.GI i) (diagonalBlock (PolyZonotope.errorBound PZ.err) i))
  E := Real.PolyZonotope.plusE PZ.E (Real.PolyZonotope.identE (PZ.q + n))
  GI := fun _ => Fin.elim0
  err := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
