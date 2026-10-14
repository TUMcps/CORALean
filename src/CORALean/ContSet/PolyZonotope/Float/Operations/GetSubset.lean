module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.getSubset`, over a floating-point scalar

One factor re-parametrized onto the sub-interval `cen ± rad` of `[-1, 1]`, as over ℝ: every
dependent generator binomially expanded into `maxExp k + 1` of them, the exponent of the
substituted factor being the term's index. The coefficients are bracketed by directed arithmetic
(`getSubsetCoef`), the stored generators are the rounded-down products, and what the rounding cost
goes into the error box by `generatorError`, added to the box the set already had.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.getSubset (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋) :
    PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := pZ.h * (pZ.maxExp k + 1)
  q := pZ.q
  c := pZ.c
  G := fun l r => pZ.getSubsetGDown k cen rad r l
  -- the substituted factor's exponent is the term's index, the others the column's own
  E := fun k' l => if k' = k then ((finProdFinEquiv.symm l).2 : ℕ)
    else pZ.E k' (finProdFinEquiv.symm l).1
  GI := pZ.GI
  I_error := pZ.I_error.plus (PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
