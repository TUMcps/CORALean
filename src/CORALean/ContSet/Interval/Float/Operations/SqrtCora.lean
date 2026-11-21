module

public import CORALean.Global.Float.SqrtDownCora
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.sqrtCora`

CORA.cpp's interval root, `[sqrt inf, sqrt sup]`, the machine's square root at both ends. The upper
end is `sqrtUp`, which at `nearest` is the machine's root. The lower end is `sqrtDownCora`, which
is that same root there and `sqrtDown` at every sound format, so the box still encloses the root
of `I` and `Interval.sqrt` is unchanged for the networks that follow its lower end.

## Inputs
* `p` – Newton steps
* `I` – interval box

## Output
* interval box enclosing the square root of `I`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sqrtCora (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => sqrtDownCora p (I.inf i)
  sup := fun i => sqrtUp p (I.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
