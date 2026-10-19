module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyLevelSet.cartProd`

CORA's `@levelSet/cartProd` at the stored data: the rows of both operands stacked, each over its
own variables, so the exponent matrices sit block-diagonally (`PolyZonotope.plusE`) and a row of
one operand reads exponent zero on every variable of the other. `and_` is the same stacking over
shared variables.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both constraint systems, each on its own block of variables and its own box. -/
def PolyLevelSet.cartProd (P₁ : PolyLevelSet n₁) (P₂ : PolyLevelSet n₂) :
    PolyLevelSet (n₁ + n₂) where
  m := P₁.m + P₂.m
  q := P₁.q + P₂.q
  A := Fin.append (fun i => Fin.append (P₁.A i) 0) (fun i => Fin.append 0 (P₂.A i))
  R := PolyZonotope.plusE P₁.R P₂.R
  b := Fin.append P₁.b P₂.b
  op := Fin.append P₁.op P₂.op
  dom := P₁.dom.append P₂.dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
