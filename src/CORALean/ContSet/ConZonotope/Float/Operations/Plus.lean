module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.Global.Block
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `ConZonotope.plus`

Generators concatenate exactly and the constraints are padded onto the wider
coefficient space, so only the center rounds and its `residual` goes into the
box — exactly as for a zonotope, the constraints adding nothing to pay for.

## Inputs
* `cZ₁` – first summand
* `cZ₂` – second summand

## Output
* enclosure of the Minkowski sum
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

def ConZonotope.plus (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := cZ₁.h + cZ₂.h
  c := fun i => addDown (cZ₁.c i) (cZ₂.c i)
  G := Fin.append cZ₁.G cZ₂.G
  P := (cZ₁.P.padLeft cZ₂.h).stackRows (HPolytope.padRight cZ₁.h cZ₂.P)
  I_error := (cZ₁.I_error.plus cZ₂.I_error).plus (Zonotope.centerResidual cZ₁.c cZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
