import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.ConZonotope.Real.Operations.KeepRows
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
import CORALean.Global.Block

/-!
# `ConZonotope.reduceKeepBy`

`Zonotope.reduceBy` with the constraints kept: the generators a partition keeps stay,
the rest are boxed into `n` fresh generators, and the constraints on the kept
coefficients are `keepRows`. The fresh coefficients are unconstrained.

Where `ConZonotope.reduce` forgets `P` before reducing, this removes the dropped
coefficients from the domain and boxes what they contributed. CORA's
`@conZonotope/reduce` does neither: it lifts the set to the zonotope `[G; A]`, reduces
that, and reads `A` and `b` back off the result, which asks for the equality system
CORA's representation carries and this one does not. Here the constraints stay a
polytope, each row projected on its own (`keepRows`), so that a row survives
intact wherever the dropped generators are unconstrained, which CORA's lifting
cannot promise. The two are not comparable as sets.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
