module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsOuterFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.OuterFactor
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# An ellipsoid as a zonotope, over a floating-point scalar

CORA's default `'outer:box'`, `zonotope(q, sqrtm(Q))`, with the factor `sqrtm(Q)` replaced by
`outerFactor`, a factor from above that `isOuterFactor` certifies (`G Gᵀ ⪰ Q`), as the float
`Ellipsoid.conPolyZono` does: the parallelotope on its columns holds the ellipsoid. It is not
CORA's parallelotope (a Cholesky factor, not the symmetric root), which no float routine here
computes. Where the factor is not certified, the zonotope is the center alone and the box
`q ± sqrt(diag(Q))` joins the error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `zonotope(E, 'outer:box')`, the factor certified from above. -/
def Ellipsoid.zonotope (E : Ellipsoid 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  -- a factor of `Q` from above
  let G : Mat 𝕋 n n := Ellipsoid.outerFactor E.Q
  -- `zonotope(q, G)` when certified, else the center with the ellipsoid's box in the error box
  if Ellipsoid.isOuterFactor E.Q G then ⟨n, E.q, fun j i => G i j, E.I_error⟩
  else ⟨0, E.q, Fin.elim0, E.I_error.plus (Interval.symmetric (Ellipsoid.boxRadius 64 E))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
