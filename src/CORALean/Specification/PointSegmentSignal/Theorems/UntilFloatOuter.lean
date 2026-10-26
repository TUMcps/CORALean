module

public import CORALean.Specification.PointSegmentSignal.Operations.Until
public import CORALean.Specification.PointSegmentSignal.Operations.UntilFloat
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilFloatOuter

@[expose] public section

/-!
# A float until shifted outward is true wherever the exact one is

If the time shift contains the difference cut at `0` (`minus`, `set_minus_outer`), then where the
until of the signals read as reals is `true` at `t ≥ 0`, so is `untilFloat` read as reals
(`intervalUntilFloat_outer`): a float `false` is an exact `false`.

## Inputs
* `shift` – the difference of two time intervals
* `lhs` – left signal
* `rhs` – right signal
* `U` – time interval
* `t` – time

## Hypotheses
* `hshift` – the shift contains the difference cut at `0`
* `ht` – the time is nonnegative

## Conclusion
* an exact `true` is a float `true`
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.untilFloat_outer (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (hshift : ∀ I J : STLInterval 𝕋, (I.set - J.set) ∩ Set.Ici 0 ⊆ (shift I J).set)
    (lhs rhs : PointSegmentSignal 𝕋) (U : STLInterval 𝕋) (t : ℝ) (ht : 0 ≤ t) : -- --- CONCL ---
    ((lhs.mapTime toReal).until U.toRealInterval (rhs.mapTime toReal)).at t = true →
      ((PointSegmentSignal.untilFloat shift lhs U rhs).mapTime toReal).at t =
        true := by -- --- PROOF ---
  -- the intervals of the signals read as reals are the float ones read as reals
  unfold PointSegmentSignal.untilFloat PointSegmentSignal.until
  rw [← PointSegmentSignal.findIntervals_mapTime, ← PointSegmentSignal.findIntervals_mapTime]
  exact PointSegmentSignal.intervalUntilFloat_outer shift hshift _ _ U t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
