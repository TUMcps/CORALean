module

public import CORALean.Global.Float.InverseTrig
public import CORALean.Global.Float.IntRound
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Capsule.piStep`: bounds of `π / 499`

The step of CORA's `linspace` over a half circle. `π = 2 arccos 0`, bounded below and above by the
sums `acosDown`, `acosUp` at `0`; the quotient by `499` rounded down with a divisor at least `499`
(`intUp`), and up with one at most `499` (`intDown`) when `ltStrict` certifies it positive, `π`
itself otherwise.

## Inputs
* `p` – precision of acos
* `k` – Newton steps for sqrt

## Output
* an interval bounding `π / 499`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.piStep (p k : ℕ) : Interval 𝕋 :=
  -- `π` from below and above
  let piLo := addDown (acosDown p k (zero : 𝕋)) (acosDown p k zero)
  let piHi := addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)
  ⟨divDown piLo (intUp 499),
    if ltStrict zero (intDown 499 : 𝕋) = true then divUp piHi (intDown 499) else piHi⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
