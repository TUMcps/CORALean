module

public import CORALean.ContSet.ConZonotope.Real.Operations.KeepEmbed
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepSlack
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.ToIneqs

@[expose] public section

/-!
# `ConZonotope.keepRows`

The constraints on the kept coefficients: every row of `P`, read at a point whose dropped
coefficients are zero and loosened by what the dropped ones can add (`keepSlack`). An equality
`a · β = b` becomes the pair `a · β ≤ b + s` and `-a · β ≤ -b + s`, by `HPolytope.toIneqs`,
`HPolytope.relax` and `HPolytope.comap` along `keepEmbed` (#174).

Each row is projected on its own, so this is an outer approximation of the exact projection onto the
kept coordinates, exact on a row the dropped coordinates do not enter, and in particular on a
polytope that leaves them unconstrained, which `reduceKeep`'s ranking drops first.

## Inputs
* `P` – constraint polytope
* `part` – partition of the generators

## Output
* the constraints on the kept coefficients
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {h q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Rows first, then each equality twice, as `≤`; no equalities remain. -/
noncomputable def ConZonotope.keepRows (P : HPolytope (Vec ℝ h))
    (part : Split (Fin h) into (Fin q) ⊕ (Fin r)) : HPolytope (Vec ℝ q) :=
  -- every row an inequality, loosened by what the dropped coefficients can add to it
  (P.toIneqs.relax fun i => ConZonotope.keepSlack part (P.rows i)).comap
    (ConZonotope.keepEmbed part)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
