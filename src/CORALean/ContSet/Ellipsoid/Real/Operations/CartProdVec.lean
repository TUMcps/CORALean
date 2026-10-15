module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.cartProdVec`

CORA's `@ellipsoid/cartProd_.m` with a point operand, which is exact: `blkdiag(E.Q, 0)` and
`[E.c; S]`, here the generator matrix padded with zero rows.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An ellipsoid times a point: the center extended by the point, the generators by zero rows. -/
def Ellipsoid.cartProdVec (E : Ellipsoid n) (v : Vec ℝ m) : Ellipsoid (n + m) where
  k := E.k
  c := Fin.append E.c v
  G := Matrix.of fun i j => Fin.addCases (fun i => E.G i j) (fun _ => 0) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
