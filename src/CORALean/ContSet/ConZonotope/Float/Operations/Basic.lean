module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp

@[expose] public section

/-!
# `ContSet/ConZonotope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ==================================  `ConZonotope.centerHi`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An upper end of `y₀ = c + G β₀`, each entry rounded upward. -/
def ConZonotope.centerHi (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 cZ.h) : Vec 𝕋 n := fun i =>
  addUp (cZ.c i) (dotUp (fun j => cZ.G j i) β₀)


-- ==================================  `ConZonotope.centerLo`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A lower end of `y₀ = c + G β₀`, each entry rounded downward. -/
def ConZonotope.centerLo (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 cZ.h) : Vec 𝕋 n := fun i =>
  addDown (cZ.c i) (dotDown (fun j => cZ.G j i) β₀)


-- =================================  `ConZonotope.quadBilUp`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `u ⬝ᵥ (Q *ᵥ v)`, from above.

The bilinear form `u ⬝ᵥ (Q *ᵥ v)` rounded up, the mirror of `quadBilDown`. -/
def ConZonotope.quadBilUp (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) : 𝕋 :=
  PolyZonotope.quadUp u (mulVecDown Q v) (mulVecUp Q v)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
