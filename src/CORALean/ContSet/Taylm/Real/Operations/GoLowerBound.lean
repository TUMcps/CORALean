module

public import CORALean.ContSet.Taylm.Real.Operations.PolyBoxBounds
public import CORALean.ContSet.Taylm.Real.Operations.Reexpand
public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Operations.Ldb
public import CORALean.ContSet.Taylm.Real.Operations.QfbLower
public import CORALean.ContSet.Taylm.Real.Operations.Hessian
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# COSY-GO's bound of a box

[1, Sec. 4]'s hierarchy for the Taylor model optimizer: the mere interval bound, the naive Taylor
model bound (the model re-expanded on the box, its polynomial by interval evaluation), LDB, and QFB
where the quadratic part is positive semidefinite, here at the box's centre. The source stops at
the first that eliminates the box; their maximum is what the hierarchy can reach.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def Taylm.goLowerBound (T : Taylm n) (ε : ℝ) (fuel : ℕ) (B : Fin n → ℝ × ℝ) : ℝ :=
  let TB := T.reexpand B
  -- the mere interval bound
  let lIN := (Taylm.polyBoxBounds T.terms B).1 + T.remInf
  -- the naive Taylor model bound, from the model re-expanded on the box
  let lTM := TB.bounds.1
  -- LDB
  let lLDB := TB.ldb ε fuel
  -- QFB at the box's centre, where the quadratic part is positive semidefinite
  let H := Taylm.hessian TB.terms
  let lQFB := if H.PosSemidef then TB.qfbLower H 0 else lTM
  max (max lIN lTM) (max lLDB lQFB)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
