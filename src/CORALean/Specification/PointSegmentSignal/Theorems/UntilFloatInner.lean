module

public import CORALean.Specification.PointSegmentSignal.Operations.Until
public import CORALean.Specification.PointSegmentSignal.Operations.UntilFloat
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilFloatInner

@[expose] public section

/-!
# A float until shifted inward is true only where the exact one is

If the time shift lies inside the difference cut at `0` (`minusInward`, `set_minusInward_inner`),
then where `untilFloat`, read as reals, is `true` at `t ≥ 0`, so is the until of the signals read
as reals (`intervalUntilFloat_inner`, the intervals found exactly by `findIntervals_mapTime`).

## Inputs
* `shift` – the difference of two time intervals
* `lhs` – left signal
* `rhs` – right signal
* `U` – time interval
* `t` – time

## Hypotheses
* `hshift` – the shift lies inside the difference cut at `0`
* `ht` – the time is nonnegative

## Conclusion
* a float `true` is an exact `true`
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

theorem PointSegmentSignal.untilFloat_inner (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (hshift : ∀ I J : STLInterval 𝕋, (shift I J).set ⊆ (I.set - J.set) ∩ Set.Ici 0)
    (lhs rhs : PointSegmentSignal 𝕋) (U : STLInterval 𝕋) (t : ℝ) (ht : 0 ≤ t) : -- --- CONCL ---
    ((PointSegmentSignal.untilFloat shift lhs U rhs).mapTime toReal).at t = true →
      ((lhs.mapTime toReal).until U.toRealInterval (rhs.mapTime toReal)).at t =
        true := by -- --- PROOF ---
  -- the intervals of the signals read as reals are the float ones read as reals
  unfold PointSegmentSignal.untilFloat PointSegmentSignal.until
  rw [← PointSegmentSignal.findIntervals_mapTime, ← PointSegmentSignal.findIntervals_mapTime]
  exact PointSegmentSignal.intervalUntilFloat_inner shift hshift _ _ U t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
