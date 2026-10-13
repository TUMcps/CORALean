module

public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepRows
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.Global.Block

@[expose] public section

/-!
# `ConZonotope.reduceKeepBy`

`Zonotope.reduceBy` with the constraints kept: the generators a partition keeps stay,
the rest are boxed into `n` fresh generators, and the constraints on the kept
coefficients are `keepRows`. The fresh coefficients are unconstrained.

Where `ConZonotope.reduce` forgets `P` before reducing, this removes the dropped
coefficients from the domain and boxes what they contributed. CORA's
`@conZonotope/reduce` lifts the equality rows with the generators and reduces that
zonotope; that is `ConZonotope.reduceLiftBy`, which uses this for the inequality rows and
the lifted box. Here, with no lifting, every row is a polytope row projected on its own
(`keepRows`), so that a row survives intact wherever the dropped generators are
unconstrained. The two are not comparable as sets.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


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
