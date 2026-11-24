module

public import CORALean.Global.Float.Log

@[expose] public section

/-!
# `logDownPos`

`log a` from below for every `0 < a`, where `logDown` asks `1 ≤ a`: the format's own `log` where
it supplies one (`elemOverride`), otherwise `-(log(1 / a))` from above, `logUp` of the quotient
rounded up. At round to nearest this is the machine's `log a`.

## Inputs
* `n` – precision of the exponential
* `k` – number of bisection steps
* `a` – float argument

## Output
* the logarithm from below, the format's own where it has one
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `log a` from below: the format's own where it has one, else `-(log(1 / a))` from above. -/
def logDownPos (n k : ℕ) (a : 𝕋) : 𝕋 :=
  match elemOverride (𝕋 := 𝕋) with
  | some e => e.log a
  | none => neg (logUp n k (divUp one a))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
