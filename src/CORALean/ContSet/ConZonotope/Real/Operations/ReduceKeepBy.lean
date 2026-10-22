module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepEmbed
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepSlack
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.ToIneqs
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.Global.Block
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepRows

@[expose] public section

/-!
# `ConZonotope.reduceKeepBy`

`Zonotope.reduceBy` with the constraints kept: the generators a partition keeps stay,
the rest are boxed into `n` fresh generators, and the constraints on the kept
coefficients are `keepRows`. The fresh coefficients are unconstrained.

Where `ConZonotope.reduce` forgets `P` before reducing, this removes the dropped coefficients from
the domain and boxes what they contributed. CORA's `@conZonotope/reduce` lifts the equality rows
with the generators first; that is `ConZonotope.reduceLiftBy`, which uses this for the inequality
rows. Here every row is projected on its own (`keepRows`); the two are not comparable as sets.

## Inputs
* `cZ` – constrained zonotope
* `part` – generator partition

## Output
* enclosing set reduced along the partition, constraints kept
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


section
open Matrix
variable {h q r : ℕ}


end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Keeps `part.left` with its constraints, boxes `part.right` into `n` unconstrained
generators; the kept constraints are `keepRows`, pulled back along the first `q`
coordinates. -/
noncomputable def ConZonotope.reduceKeepBy (cZ : ConZonotope (Vec ℝ n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) : ConZonotope (Vec ℝ n) where
  h := q + n
  c := cZ.c
  G := (cZ.zonotope.reduceBy part).G
  P := (ConZonotope.keepRows cZ.P part).comap (blockLeft q n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
