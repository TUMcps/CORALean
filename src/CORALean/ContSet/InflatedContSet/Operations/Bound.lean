module

public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.Interval.Float.Operations.OfBounds

@[expose] public section

/-!
# Bounding an inflated representation in a direction

The set is a nominal one plus an error box, so a direction sees the sum of what
each reaches — bound the two parts and add them upward. Every float
representation with an ambient error box answers a linear program this way, and
none of them has to say so separately.

The nominal bound is the exact layer's problem, unchanged: the box only pays for
the rounding that put it there.

## Inputs
* `c` – linear functional
* `s` – inflated set
* `u` – float bound of the nominal part
* `v` – float bound of the error box

## Output
* float bound of `c` on the whole inflated set
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N (Vec 𝕋 n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

def InflatedContSet.boundOfParts {c : Vec ℝ n →ₗ[ℝ] ℝ} {s : S}
    (u : FloatBound 𝕋 (nominalSet s) c) (v : FloatBound 𝕋 (I_error s).construct c) :
    FloatBound 𝕋 (InflatedContSet.construct s) c :=
  u.add v

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
