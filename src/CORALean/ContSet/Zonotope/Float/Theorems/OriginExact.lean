module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

@[expose] public section

/-!
# `Zonotope.origin` is exactly the origin

`zero` reads as `0`, so the stored center is the exact layer's origin and the
point theorem gives `{0}`.

## Inputs
* `n` – dimension

## Hypotheses
* none

## Conclusion
* origin zonotope denotes the zero vector only
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.origin_exact (n : ℕ) :
    (Zonotope.origin n : Zonotope (Vec 𝕋 n)).construct = {0} := by
  have h : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  rw [Zonotope.origin, Zonotope.construct_point, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
