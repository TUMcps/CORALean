module

public import CORALean.Global.Float.InverseTrig
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.acos`

Decreasing, so the corners swap: `acosDown` at the upper bound and `acosUp` at the lower one
(`Global/Float/InverseTrig`), sound for every box. `p` is the number of halvings of the sine and
cosine, `k` the number of bisection and Newton steps.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `I` – interval box

## Output
* interval box enclosing the arccosine of `I`
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

def Interval.acos (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => acosDown p k (I.sup i)
  sup := fun i => acosUp p k (I.inf i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
