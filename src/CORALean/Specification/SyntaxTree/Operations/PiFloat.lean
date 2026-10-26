module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.InverseTrig

@[expose] public section

/-!
# `pi` over a float scalar

MATLAB's `pi` as an interval of floats: `π = 2 arccos 0`, bounded below and above by the sums of
`acosDown` and `acosUp` at `0` (the way `Capsule.piStep` brackets it). The shifts by `π` and `2 pi
k` of the contractions of `sin`, `cos` and `tan` round with it.

## Inputs
* `p` – precision of acos
* `k` – Newton steps for sqrt

## Output
* an interval of floats containing `π`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pi` as the bounds `2 acosDown(0)` and `2 acosUp(0)`. -/
def SyntaxTree.piFloat (p k : ℕ) : Float.Interval 𝕋 :=
  ⟨addDown (acosDown p k (zero : 𝕋)) (acosDown p k zero),
    addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
