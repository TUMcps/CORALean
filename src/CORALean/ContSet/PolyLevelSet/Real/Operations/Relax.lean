module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyLevelSet.relax`

Each row loosened by a variable of its own: row `i` becomes `(A μ_R(x) - b)ᵢ + sᵢ yᵢ ⋈ᵢ 0` over
the variables `(x, y)`, `yᵢ` entering row `i` alone, as the monomial `yᵢ` with coefficient `sᵢ`.
Bounding `y` to `[-1, 1]ᵐ` then widens an equation to `|(A μ_R(x))ᵢ - bᵢ| ≤ |sᵢ|`
(`exists_relax_iff`).

Not one of CORA's operations: it is what a float constraint's per-row slack `b_error` denotes
(`Float.PolyLevelSet.construct`), and how a constrained polynomial zonotope holds such a slack as a
factor per row (`ConPolyZono.relax`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` widened by `sᵢ yᵢ`, `yᵢ` a fresh variable read by that row alone. -/
def PolyLevelSet.relax (P : PolyLevelSet n) (s : Vec ℝ P.m) : PolyLevelSet (n + P.m) where
  m := P.m
  q := P.q + P.m
  A := fun i => Fin.append (P.A i) (Pi.single i (s i))
  R := PolyZonotope.plusE P.R (PolyZonotope.identE P.m)
  b := P.b
  op := P.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
