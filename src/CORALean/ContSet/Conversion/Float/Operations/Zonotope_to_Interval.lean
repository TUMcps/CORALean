module

public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Data.Matrix.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A zonotope as a box, over a floating-point scalar

## Inputs
* `Z` – zonotope

## Output
* interval enclosing the zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.interval (Z : Zonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => addDown (subDown (Z.c i) (radius (fun i j => Z.G j i) i)) (Z.I_error.inf i)
  sup := fun i => addUp (addUp (Z.c i) (radius (fun i j => Z.G j i) i)) (Z.I_error.sup i)

/-- The box of a zonotope of matrices: the center plus and minus the sum of the absolute generators,
widened by the error box. -/
def Zonotope.matInterval {m : ℕ} (Z : Zonotope (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  let r : Mat 𝕋 m n := fun i j => sumUp fun k => absolute (Z.G k i j)   -- Σ |G_k|
  ⟨fun i j => addDown (subDown (Z.c i j) (r i j)) (Z.I_error.inf i j),
   fun i j => addUp (addUp (Z.c i j) (r i j)) (Z.I_error.sup i j)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
