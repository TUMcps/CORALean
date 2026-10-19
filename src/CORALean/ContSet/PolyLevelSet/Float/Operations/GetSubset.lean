module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Lhs
public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDiff
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `PolyLevelSet.getSubset` over a floating-point scalar

Variable `k` re-parametrized onto `cen ± rad`, as over ℝ: `PolyZonotope.getSubset` at the rows'
polynomial part (`lhs`). The coefficients are stored rounded down, and each row's slack is widened
by the row radius of what they lost, which bounds the whole row's error wherever the monomials
are in `[-1, 1]` (`mem_getSubset_of_real`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows at `xₖ ↦ cen + rad xₖ`, the slack widened by what the stored coefficients lost. -/
def PolyLevelSet.getSubset (P : PolyLevelSet 𝕋 n) (k : Fin n) (cen rad : 𝕋) : PolyLevelSet 𝕋 n where
  m := P.m
  q := (P.lhs.getSubset k cen rad).h
  A i l := (P.lhs.getSubset k cen rad).G l i
  R := (P.lhs.getSubset k cen rad).E
  b := P.b
  -- the slack grows by the stored entries' rounding, scaled by monomials in `[-1, 1]`
  b_error i := addUp (absolute (P.b_error i)) (radius (P.lhs.getSubsetGDiff k cen rad) i)
  op := P.op
  dom := P.dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
