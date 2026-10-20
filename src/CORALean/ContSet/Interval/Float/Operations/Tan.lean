module

public import CORALean.Global.Float.Tan
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.tan`

Increasing on `(-π/2, π/2)`, so `tanDown` at the lower bound and `tanUp` at the upper one
(`Global/Float/Tan`). The bounds are sound where the computed cosine at each corner is positive,
which `Interval.tan_outer` takes as a hypothesis beside the principal-branch one. `p` is the number
of halvings of the sine and cosine.

## Inputs
* `p` – halving count
* `I` – interval box

## Output
* interval box enclosing the tangent of `I`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.tan (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => tanDown p (I.inf i)
  sup := fun i => tanUp p (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
