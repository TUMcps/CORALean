module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
public import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# `ContSet/Ellipsoid/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- ======================================  `Ellipsoid.G`  ======================================= --
-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)

/-- The generator matrix `Q^(1/2)`, CORA's `sqrtm(Q)`: symmetric, and `G G = Q`. The set is its
image of the unit ball (`Theorems/ConstructEqSqrt`). -/
noncomputable def Ellipsoid.G (E : Ellipsoid n) : Mat ℝ n n := CFC.sqrt E.Q


-- ===================================  `Ellipsoid.pullback`  =================================== --
-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The direction pulled back into generator space, which is what the support
value is the length of. -/
noncomputable def Ellipsoid.pullback (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ n :=
  E.Gᵀ *ᵥ dualVec c


-- ==============================  `Ellipsoid.representsa_origin`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ellipsoid/representsa_` at `origin`.

CORA's `@ellipsoid/representsa_` at type `origin` with tolerance `0`: a point at `q = 0`. -/
def Ellipsoid.representsa_origin (E : Ellipsoid n) : Prop := E.q = 0 ∧ E.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
