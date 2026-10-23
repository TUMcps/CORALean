module

public import CORALean.Specification.STLInterval.Instances
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.ToRealInterval
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# The constructor at a float scalar, read as reals

Over a float scalar `𝕋` the constructor `stlInterval` decides emptiness on the reals the bounds
denote, so the float interval it builds, read as reals, is the one it builds from those reals.

## Inputs
* `lb` – lower bound
* `ub` – upper bound, or `inf`
* `lc` – whether the lower end is closed
* `rc` – whether the upper end is closed

## Hypotheses
* `hlb` – the lower bound is at least `0`

## Conclusion
* the float interval, read as reals, is the interval of the denoted bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.stlInterval_toRealInterval (lb : 𝕋) (ub : WithTop 𝕋) (lc rc : Bool)
    (hlb : 0 ≤ toReal lb) :
    (STLInterval.stlInterval lb ub lc rc hlb).toRealInterval =
      STLInterval.stlInterval (toReal lb) (ub.map toReal) lc rc hlb := by
  -- both decide the same condition on the same reals
  cases ub <;> unfold STLInterval.stlInterval <;>
    simp only [WithTop.map_top, WithTop.map_coe, STLInterval.toEReal_coe, STLInterval.toEReal_top,
      toReal_real] <;> split_ifs <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
