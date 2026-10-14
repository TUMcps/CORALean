module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `ContSet/Ellipsoid/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `Ellipsoid.centre`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `@ellipsoid/center` returns the field `q`: the stored centre, in `𝕋`. -/
def Ellipsoid.centre (E : Ellipsoid 𝕋 n) : Vec 𝕋 n := E.q

end CORALean.Float


-- ===================================  `Ellipsoid.enclose₂`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- CORA's `enclose(E, E2)`, `convHull(E, E2)`: the hull `orOA` of the two ellipsoids, an argument
owing the contract that its result contains both (CORA's SDP-solver `or(E, E2, 'outer')`). -/
def Ellipsoid.enclose₂ (orOA : Ellipsoid 𝕋 n → Ellipsoid 𝕋 n → Ellipsoid 𝕋 n)
    (E E2 : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  orOA E E2

end CORALean.Float


-- ====================================  `Ellipsoid.plusG`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The two scaled generator blocks side by side, each rounded down. -/
def Ellipsoid.plusG (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Mat 𝕋 n (E₁.k + E₂.k) :=
  fun i => Fin.append (fun j => mulDown s₁ (E₁.G i j)) (fun j => mulDown s₂ (E₂.G i j))

end CORALean.Float


-- ===================================  `Ellipsoid.plusGap`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- How far each stored generator can be from its exact scaling. -/
def Ellipsoid.plusGap (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Mat 𝕋 n (E₁.k + E₂.k) :=
  fun i => Fin.append
    (fun j => subUp (mulUp s₁ (E₁.G i j)) (mulDown s₁ (E₁.G i j)))
    (fun j => subUp (mulUp s₂ (E₂.G i j)) (mulDown s₂ (E₂.G i j)))

end CORALean.Float


-- =================================  `Ellipsoid.pullbackAbs`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The magnitude of the direction pulled back into generator space, coordinate
by coordinate. `sqSumUp` of this is what a candidate is checked against. -/
def Ellipsoid.pullbackAbs (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) (j : Fin E.k) : 𝕋 :=
  maximum (dotUp a fun i => E.G i j) (neg (dotDown a fun i => E.G i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
