module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Lhs
public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset

@[expose] public section

/-!
# `PolyLevelSet.getSubset`

Variable `r` re-parametrized onto `cen ± rad`: every row read at `x` with `xᵣ` replaced by
`cen + rad xᵣ` (`eval_getSubset`). The monomials are expanded binomially by
`PolyZonotope.getSubset` at the rows' polynomial part (`lhs`), and `b` and the operators stand.
CORA's `@conPolyZono/getSubset` at its constraint, the part of it that is the level set's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
