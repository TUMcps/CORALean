module

public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombGDiff
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

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

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.linComb (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := cZ₁.h + cZ₂.h + 1
  c := Zonotope.midpoint cZ₁.c cZ₂.c
  G := Fin.append (Fin.append cZ₁.G cZ₂.G)
    fun _ : Fin 1 => fun i => half (subDown (cZ₁.c i) (cZ₂.c i))
  P := ((cZ₁.P.stackRows (HPolytope.unitBox 𝕋 cZ₁.h)).halfScaledLeft cZ₂.h).stackRows
    (HPolytope.halfScaledRight cZ₁.h (cZ₂.P.stackRows (HPolytope.unitBox 𝕋 cZ₂.h)))
  I_error := (cZ₁.I_error.linComb cZ₂.I_error).plus
    ((Zonotope.midpointResidual cZ₁.c cZ₂.c).plus
      (Zonotope.generatorError (ConZonotope.linCombGDiff cZ₁ cZ₂)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
