module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `ContSet/Ellipsoid/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ====================================  `Ellipsoid.center`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@ellipsoid/center` returns the field `q`: the stored center, in `𝕋`. -/
def Ellipsoid.center (E : Ellipsoid 𝕋 n) : Vec 𝕋 n := E.q


-- ===================================  `Ellipsoid.enclose₂`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- CORA's `enclose(E, E2)`, `convHull(E, E2)`: the hull `orOA` of the two ellipsoids, an argument
owing the contract that its result contains both (CORA's SDP-solver `or(E, E2, 'outer')`). -/
def Ellipsoid.enclose₂ (orOA : Ellipsoid 𝕋 n → Ellipsoid 𝕋 n → Ellipsoid 𝕋 n)
    (E E2 : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  orOA E E2


-- ===================================  `Ellipsoid.quadDown`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aᵀ Q a` rounded down, as `quadUp` from the other side. -/
def Ellipsoid.quadDown (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) : 𝕋 :=
  sumDown fun i =>
    minimum (mulDown (a i) (mulVecDown E.Q a i)) (mulDown (a i) (mulVecUp E.Q a i))


-- ====================================  `Ellipsoid.quadUp`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aᵀ Q a` rounded up: `Q a` between its two roundings, each coordinate's product with `aᵢ` at
the end of the bracket that makes it larger. -/
def Ellipsoid.quadUp (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) : 𝕋 :=
  sumUp fun i => maximum (mulUp (a i) (mulVecDown E.Q a i)) (mulUp (a i) (mulVecUp E.Q a i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
