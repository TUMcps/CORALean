module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiffError
public import CORALean.ContSet.PolyZonotope.Float.Operations.LinCombGIDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.Midpoint
public import CORALean.ContSet.PolyZonotope.Float.Operations.MidpointResidual
public import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.linComb`

The exact layer's three dependent blocks, and nothing in any of them rounds: halving and
negation are exact, so `½G₁`, `½G₂` and `-½G₂` are copies, and `linCombE` is over ℕ. What is
left is three vectors' worth of rounding. The center and the sliding generator are what a
zonotope's `linComb` already pays (a `residual`, and a symmetric box). The independent block
pairs, so `generatorError` charges its whole matrix; `Zonotope.pairSum`, `pairDiff` and
`generatorError` are borrowed, as CORA runs `zonotope/enclose` on it.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Output
* polynomial zonotope enclosing the linear combinations
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.linComb (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ₁.p + pZ₂.p + 1
  h := pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1)
  q := pZ₁.q + pZ₂.q
  c := PolyZonotope.midpoint pZ₁.c pZ₂.c
  G := Fin.append
        (Fin.append (fun l i => half (pZ₁.G l i)) (fun l i => half (pZ₂.G l i)))
        (Fin.append
          (Fin.append (fun l i => half (pZ₁.G l i)) (fun l i => neg (half (pZ₂.G l i))))
          (fun _ : Fin 1 => PolyZonotope.halfDiff pZ₁.c pZ₂.c))
  E := Real.PolyZonotope.linCombE pZ₁.E pZ₂.E
  GI := fun j i => PolyZonotope.linCombGI addDown subDown pZ₁ pZ₂ i j
  I_error := (pZ₁.I_error.linComb pZ₂.I_error).plus
    ((PolyZonotope.midpointResidual pZ₁.c pZ₂.c).plus
      ((PolyZonotope.halfDiffError pZ₁.c pZ₂.c).plus
        (Zonotope.generatorError (PolyZonotope.linCombGIDiff pZ₁ pZ₂))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
