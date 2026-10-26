module

public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilFloatSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilSpec
public import CORALean.Specification.STLInterval.Theorems.LeftClosureToRealInterval
public import CORALean.Specification.STLInterval.Theorems.RightClosureToRealInterval

@[expose] public section

/-!
# A float until of intervals shifted inward is true only where the exact one is

If the time shift lies inside the difference (cut at `0`), as `minusInward` does
(`set_minusInward_inner`), then where `intervalUntilFloat`, read as reals, is `true` at `t ≥ 0`,
so is `intervalUntil` of the intervals read as reals: every shifted interval of a pair lies inside
the exact one.

## Inputs
* `shift` – the difference of two time intervals
* `lhsInt` – intervals of the left signal
* `rhsInt` – intervals of the right signal
* `U` – until interval
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

theorem PointSegmentSignal.intervalUntilFloat_inner
    (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (hshift : ∀ I J : STLInterval 𝕋, (shift I J).set ⊆ (I.set - J.set) ∩ Set.Ici 0)
    (lhsInt rhsInt : List (STLInterval 𝕋)) (U : STLInterval 𝕋) (t : ℝ)
    (ht : 0 ≤ t) : -- --- CONCL ---
    ((PointSegmentSignal.intervalUntilFloat shift lhsInt U rhsInt).mapTime toReal).at t = true →
      (PointSegmentSignal.intervalUntil (lhsInt.map STLInterval.toRealInterval)
        U.toRealInterval (rhsInt.map STLInterval.toRealInterval)).at t = true := by -- --- PROOF ---
  obtain ⟨hU', -, hf⟩ := PointSegmentSignal.intervalUntilFloat_spec shift lhsInt rhsInt U
  rw [hf t ht, ((PointSegmentSignal.intervalUntil_spec _ _ _).2 t ht)]
  rintro (⟨L, hL, R, hR, hs, hl⟩ | ⟨h0, R, hR, hr⟩)
  · -- a shifted time is a difference of a time of the pair and a nonzero until time
    obtain ⟨⟨a, ha, b, hb, hab⟩, -⟩ := hshift _ _ hs
    rw [STLInterval.set_and_, Set.mem_inter_iff] at ha
    rw [hU', Set.mem_sdiff, Set.mem_singleton_iff] at hb
    refine Or.inl ⟨L.toRealInterval, List.mem_map_of_mem hL, R.toRealInterval,
      List.mem_map_of_mem hR, a, by rw [STLInterval.set_toRealInterval]; exact ha.1, ?_, ?_, ?_,
      fun e => hb.2 (by linarith)⟩
    · rw [← STLInterval.rightClosure_toRealInterval, STLInterval.set_toRealInterval]
      exact ha.2
    · rw [← STLInterval.leftClosure_toRealInterval, STLInterval.set_toRealInterval]
      exact hl
    · rw [STLInterval.set_toRealInterval, show a - t = b by linarith]
      exact hb.1
  · -- the right-hand side holds at `t` itself
    exact Or.inr ⟨by rw [STLInterval.set_toRealInterval]; exact h0, R.toRealInterval,
      List.mem_map_of_mem hR, by rw [STLInterval.set_toRealInterval]; exact hr⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
