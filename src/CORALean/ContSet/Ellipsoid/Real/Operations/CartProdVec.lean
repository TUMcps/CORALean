import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.cartProdVec`

CORA's `@ellipsoid/cartProd_.m` with a point operand, which is exact: `blkdiag(E.Q, 0)` and
`[E.q; S]`, here the generator matrix padded with zero rows.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An ellipsoid times a point: the centre extended by the point, the generators by zero rows. -/
def Ellipsoid.cartProdVec (E : Ellipsoid n) (v : Vec ℝ m) : Ellipsoid (n + m) where
  k := E.k
  q := Fin.append E.q v
  G := Matrix.of fun i j => Fin.addCases (fun i => E.G i j) (fun _ => 0) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
