module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.and_`

CORA's `@levelSet/and_` at the stored data: the rows of both operands stacked, each over its own
monomials, so the monomial list is the two exponent matrices side by side and a row of one operand
is blind to the other's monomials.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both constraint systems, each with its own operators, over both monomial lists. -/
def PolyLevelSet.and_ (P₁ P₂ : PolyLevelSet n) : PolyLevelSet n where
  m := P₁.m + P₂.m
  q := P₁.q + P₂.q
  A := Fin.append (fun i => Fin.append (P₁.A i) 0) (fun i => Fin.append 0 (P₂.A i))
  R k := Fin.append (P₁.R k) (P₂.R k)
  b := Fin.append P₁.b P₂.b
  op := Fin.append P₁.op P₂.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
