module

public import CORALean.Global.Float.InverseTrig
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.atan`

Increasing, so `atanDown` at the lower bound and `atanUp` at the upper one
(`Global/Float/InverseTrig`), sound for every box. `p` is the number of halvings of the sine and
cosine, `k` the number of bisection and Newton steps.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `I` – interval box

## Output
* interval box enclosing the arctangent of `I`
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

def Interval.atan (p k : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => atanDown p k (I.inf i)
  sup := fun i => atanUp p k (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
