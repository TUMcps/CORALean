module

public import CORALean.ContSet.OptEmpty.OptEmpty
public import CORALean.ContSet.Ellipsoid.Float.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.ExcludesPoint

@[expose] public section

/-!
# `Ellipsoid.andPoint`, over a floating-point scalar

CORA's `@ellipsoid/and_.m` for a point `p`: the point as a degenerate ellipsoid if `p ∈ E`, and
`∅` otherwise. The exact layer decides `p ∈ E` classically; here the decision is two certified
tests, each sound only at `true`: `containsPoint` with the solve `w` of `Q w = p - q` the caller
proposes for `p ∈ E`, and `excludesPoint` with a separating direction `a` and the length `s` it
needs for `p ∉ E`. When neither certifies, the point is returned: `{p} ⊇ E ∩ {p}` whatever the
truth, so the answer stays an enclosure, exact on both certified branches.

## Inputs
* `E` – ellipsoid
* `p` – point
* `w` – solve of `Q w = p - q`
* `a` – separating direction
* `s` – length bounding `√(aᵀ Q a)`

## Output
* the point if `p ∈ E` or undecided, empty if certified outside
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `and_(E, p)` for a point `p`: certified in, the point; certified out, `∅`; undecided, the
point again, an outer answer. -/
def Ellipsoid.andPoint (E : Ellipsoid 𝕋 n) (p w : Vec 𝕋 n) (a : Vec 𝕋 n) (s : 𝕋) :
    OptEmpty (Ellipsoid 𝕋 n) :=
  if E.containsPoint p w then .of (Ellipsoid.ofPoint p)
  else if E.excludesPoint p a s then .empty
  else .of (Ellipsoid.ofPoint p)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
