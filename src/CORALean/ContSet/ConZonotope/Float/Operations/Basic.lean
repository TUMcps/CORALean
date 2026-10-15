module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp
public import CORALean.ContSet.Zonotope.Float.Operations.Reduce
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

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


-- ===================================  `ConZonotope.reduce`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---

/-- Above the requested order, the enclosing zonotope is reduced and the constraints
dropped; at or below it, nothing happens and the constraints survive. As over ℝ. -/
def ConZonotope.reduce (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (o : ℕ) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  if o * n < cZ.h then (cZ.zonotope.reduce o).conZonotope else cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
