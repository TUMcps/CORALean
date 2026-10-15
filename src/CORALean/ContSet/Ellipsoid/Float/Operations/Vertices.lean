module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.vertices`, over a floating-point scalar

The one-dimensional case, the only one CORA supports. The ends are the center give or take the
length `ρ = ‖G₀‖₂` of the generator row (`normUp`, `k` Newton steps, rounded up), the lower one
rounded down and the upper one up, each shifted by its end of the error box. Both are always
returned: CORA's single-vertex case (the two agree within tolerance) is not modelled, so for a
point the list holds that point twice. The statement is an outer one, the ellipsoid lies in the
hull of the two points.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.vertices (k : ℕ) (E : Ellipsoid 𝕋 1) : List (Vec 𝕋 1) :=
  let ρ := normUp k fun j => E.G 0 j
  [fun _ => addDown (subDown (E.c 0) ρ) (E.I_error.inf 0),
   fun _ => addUp (addUp (E.c 0) ρ) (E.I_error.sup 0)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
