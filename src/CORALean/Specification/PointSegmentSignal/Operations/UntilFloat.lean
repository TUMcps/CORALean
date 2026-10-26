module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntilFloat

@[expose] public section

/-!
# The until of two signals over a float scalar

`sig = until(lhs,interval,rhs)` of `pointSegmentSignal` with time stamps in `𝕋`: the until of the
intervals where the signals are `true` (`intervalUntilFloat`), with the time shift `shift`;
`minusInward` makes it true only where the exact until is (`untilFloat_inner`), `minus` true
wherever it is (`untilFloat_outer`).

## Inputs
* `shift` – the difference of two time intervals
* `lhs` – left signal
* `interval` – time interval
* `rhs` – right signal

## Output
* the until signal
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = until(lhs,interval,rhs)` with the time shift `shift`. -/
def PointSegmentSignal.untilFloat (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (lhs : PointSegmentSignal 𝕋) (interval : STLInterval 𝕋) (rhs : PointSegmentSignal 𝕋) :
    PointSegmentSignal 𝕋 :=
  -- 1. find the positive intervals
  let lhsInt := lhs.findIntervals
  let rhsInt := rhs.findIntervals
  -- 2. set to true wherever we find a witness for until
  PointSegmentSignal.intervalUntilFloat shift lhsInt interval rhsInt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
