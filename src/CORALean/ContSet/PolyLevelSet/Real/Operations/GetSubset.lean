module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Lhs
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# `PolyLevelSet.getSubset`

Variable `r` re-parametrized onto `cen ± rad`: every row read at `x` with `xᵣ` replaced by
`cen + rad xᵣ` (`eval_getSubset`). The monomials are expanded binomially by
`PolyZonotope.getSubset` at the rows' polynomial part (`lhs`), and `b`, the operators and the box
stand, so a point of the result is one of the box at which the substituted rows hold
(`mem_getSubset_iff`). CORA's `@conPolyZono/getSubset` at its constraint, the level set's part.

## Inputs
* `P` – polynomial level set
* `r` – variable index
* `cen` – new center of the variable
* `rad` – new radius of the variable

## Output
* the level set with variable `r` rescaled onto `cen ± rad`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows at `xᵣ ↦ cen + rad xᵣ`, their monomials binomially expanded. -/
def PolyLevelSet.getSubset (P : PolyLevelSet n) (r : Fin n) (cen rad : ℝ) : PolyLevelSet n where
  m := P.m
  q := (P.lhs.getSubset r cen rad).h
  A i l := (P.lhs.getSubset r cen rad).G l i
  R := (P.lhs.getSubset r cen rad).E
  b := P.b
  op := P.op
  dom := P.dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
