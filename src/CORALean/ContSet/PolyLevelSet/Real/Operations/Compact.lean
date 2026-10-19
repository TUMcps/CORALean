module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactIdx
public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactKeep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

@[expose] public section

/-!
# `PolyLevelSet.compact`

The monomial list without repeats: monomials with equal exponent columns merged, their coefficient
columns added, and the columns that add up to zero dropped — `PolyZonotope.compact`'s merge, with
the coefficient columns `A_(·,j)` as the generators. The rows, their right-hand sides and their
operators stand, so the set does too (`compact_exact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns merged, the zero coefficient columns gone. -/
noncomputable def PolyLevelSet.compact (P : PolyLevelSet n) : PolyLevelSet n where
  m := P.m
  q := (PolyZonotope.compactKeep P.R (fun l i => P.A i l)).card
  A := fun i l => PolyZonotope.fiberSum (PolyZonotope.rep P.R) (fun l i => P.A i l)
    (PolyZonotope.compactIdx P.R (fun l i => P.A i l) l) i
  R := fun k l => P.R k (PolyZonotope.compactIdx P.R (fun l i => P.A i l) l)
  b := P.b
  op := P.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
