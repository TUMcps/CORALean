module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.CholFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.PdCheck
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `Ellipsoid.isFullDim`, over a floating-point scalar

CORA's `@ellipsoid/isFullDim` asks for `rank(Q) = n`, which rounding cannot decide. A sound test
instead certifies `Q` positive definite: symmetric, and `Q - L Lᵀ` strictly diagonally dominant
for the factor `cholFactor` proposes (`pdCheck`). The error box must be nonempty (`inf ≤ sup` by
`le`), so that the set is a translate-containing sum. Only `true` is certain.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isFullDim (E : Ellipsoid 𝕋 n) : Bool :=
  Ellipsoid.isSymm E.Q && Ellipsoid.pdCheck (Interval.point E.Q) (Ellipsoid.cholFactor 64 E.Q) &&
    (List.finRange n).all fun i => le (E.I_error.inf i) (E.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
