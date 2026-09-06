import CORALean.ContSet.ConZonotope.Float.Operations.LinCombGDiff
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
import CORALean.ContSet.Interval.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Operations.LinComb

/-!
# `ConZonotope.linComb`

The exact operation's shape, rounded, and almost nothing rounds: the generator
blocks are copied, the constraint rows are copied and halved, and halving is
exact. Only the centre and the generator spanning the half-difference of the
centres are arithmetic, so the box carries a midpoint residual and a generator
error over that one column.

Each block's constraints are weighted by the trailing coefficient — `λ` on the
left and `1 - λ` on the right — and the unit box is weighted with them, which is
what pins a block to zero as its weight vanishes. The float polytope has no
`comap`, so the block a set of rows reads is fixed by where they are padded
rather than by a map, which is why the two sides are two operations.

The blocks are not paired the way a zonotope's are: pairing merges two
coefficients into one, and each block's constraints have to read them apart.
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

def ConZonotope.linComb (C₁ C₂ : ConZonotope 𝕋 n) : ConZonotope 𝕋 n where
  h := C₁.h + C₂.h + 1
  c := Zonotope.midpoint C₁.c C₂.c
  G := fun i => Fin.append (Fin.append (C₁.G i) (C₂.G i))
    fun _ : Fin 1 => half (subDown (C₁.c i) (C₂.c i))
  P := ((C₁.P.and (HPolytope.unitBox 𝕋 C₁.h)).halfScaledLeft C₂.h).and
    (HPolytope.halfScaledRight C₁.h (C₂.P.and (HPolytope.unitBox 𝕋 C₂.h)))
  E := (C₁.E.linComb C₂.E).plus
    ((Zonotope.midpointResidual C₁.c C₂.c).plus
      (Zonotope.generatorError (ConZonotope.linCombGDiff C₁ C₂)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
