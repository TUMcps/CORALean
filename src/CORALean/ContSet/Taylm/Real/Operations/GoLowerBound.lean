module

public import CORALean.ContSet.Taylm.Real.Operations.PolyBoxBounds
public import CORALean.ContSet.Taylm.Real.Operations.Ldb
public import CORALean.ContSet.Taylm.Real.Operations.QfbLower
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# COSY-GO's bound of a box

[1, Sec. 4]'s hierarchy for the Taylor model optimizer: the mere interval bound, the naive Taylor
model bound (the model re-expanded on the box, its polynomial by interval evaluation), LDB, and QFB
where the quadratic part is positive semidefinite, here at the box's center. The source stops at
the first that eliminates the box; their maximum is what the hierarchy can reach.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Hessian of the terms at `0`, as CORA's `optLinQuad` reads it: twice the coefficient of `xₖ²`
on the diagonal, the coefficient of `xₖxₗ` off it. The `H` of [1, Sec. 3]. -/
noncomputable def Taylm.aux_hessian (L : List (ℝ × (Fin n → ℕ))) : Mat ℝ n n := fun k l =>
  ((L.filter fun a => decide (a.2 = Pi.single k 1 + Pi.single l 1)).map Prod.fst).sum *
    (if k = l then 2 else 1)


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def Taylm.goLowerBound (T : Taylm n) (ε : ℝ) (fuel : ℕ) (B : Fin n → Interval ℝ) : ℝ
    :=
  let TB := T.reexpand B
  -- the mere interval bound
  let lIN := (Taylm.polyBoxBounds T.terms B).inf + T.rem.inf
  -- the naive Taylor model bound, from the model re-expanded on the box
  let lTM := TB.bounds.inf
  -- LDB
  let lLDB := TB.ldb ε fuel
  -- QFB at the box's center, where the quadratic part is positive semidefinite
  let H := Taylm.aux_hessian TB.terms
  let lQFB := if H.PosSemidef then TB.qfbLower H 0 else lTM
  max (max lIN lTM) (max lLDB lQFB)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
