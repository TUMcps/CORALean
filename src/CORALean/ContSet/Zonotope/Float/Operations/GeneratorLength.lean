module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Zonotope.generatorLength`, over a floating-point scalar

CORA's `@zonotope/generatorLength.m`: `vecnorm(Z.G)`, the Euclidean length of each generator.
The length of generator `j` is rounded up (`normUp`, `k` Newton steps, `Global/Float/Sqrt`), so
the stored number is at least the length of the generator the stored floats describe. The error
box is not part of the generators, as in CORA, where `Z.G` has no error term.

## Inputs
* `k` – Newton steps for the norm
* `Z` – zonotope
* `j` – generator index

## Output
* length of generator `j`, rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The length of generator `j`, rounded up. -/
def Zonotope.generatorLength (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) : 𝕋 :=
  normUp k (Z.G j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
