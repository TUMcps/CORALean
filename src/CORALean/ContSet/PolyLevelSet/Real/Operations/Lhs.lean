module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.lhs`

The rows' polynomial part `x ↦ A μ_R(x)` as a polynomial zonotope over `Vec ℝ m`: the columns of
`A` as dependent generators at the exponents `R`, no center and no independent generators, so its
point at `x` is `A μ_R(x)` (`point_lhs`). CORA's `polyZonotope(-b, A, [], R)` inside
`@conPolyZono/getSubset`, with the offset left out: `b` takes no part in an operation on the
monomials, which is what this is for, applying a `PolyZonotope` operation to the rows.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows' polynomial part, as a polynomial zonotope over `Vec ℝ m`. -/
def PolyLevelSet.lhs (P : PolyLevelSet n) : PolyZonotope (Vec ℝ P.m) where
  p := n
  h := P.q
  q := 0
  c := 0
  G l i := P.A i l
  E := P.R
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
