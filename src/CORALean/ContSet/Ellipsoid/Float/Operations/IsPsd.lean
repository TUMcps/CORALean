module

public import CORALean.ContSet.Ellipsoid.Float.Operations.IsSymm
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.CholFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.PsdCheck
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# A stored shape matrix, certified positive semi-definite

CORA's constructor checks `Q` symmetric and positive semi-definite up to a tolerance, by its
eigenvalues; this is the check a float operation can prove something from: the stored floats
symmetric, and `Q - L Lᵀ` diagonally dominant for the factor `cholFactor` proposes
(`psdCheck`). `false` says nothing about `Q`; `true` makes the nominal part the ellipsoid of `Q`
(`Theorems/IsPsdSound`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Q` is certified symmetric and positive semi-definite. -/
def Ellipsoid.isPsd (Q : Mat 𝕋 n n) : Bool :=
  Ellipsoid.isSymm Q && Ellipsoid.psdCheck (Interval.point Q) (Ellipsoid.cholFactor 64 Q)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
