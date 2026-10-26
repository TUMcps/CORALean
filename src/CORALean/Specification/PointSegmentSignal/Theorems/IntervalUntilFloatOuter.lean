module

public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilFloatSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilSpec
public import CORALean.Specification.STLInterval.Theorems.LeftClosureToRealInterval
public import CORALean.Specification.STLInterval.Theorems.RightClosureToRealInterval

@[expose] public section

/-!
# A float until of intervals shifted outward is true wherever the exact one is

If the time shift contains the difference (cut at `0`), as `minus` does (`set_minus_outer`), then
where `intervalUntil` of the intervals read as reals is `true` at `t ≥ 0`, so is
`intervalUntilFloat` read as reals: a float `false` is an exact `false`.

## Inputs
* `shift` – the difference of two time intervals
* `lhsInt` – intervals of the left signal
* `rhsInt` – intervals of the right signal
* `U` – until interval
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

theorem PointSegmentSignal.intervalUntilFloat_outer
    (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (hshift : ∀ I J : STLInterval 𝕋, (I.set - J.set) ∩ Set.Ici 0 ⊆ (shift I J).set)
    (lhsInt rhsInt : List (STLInterval 𝕋)) (U : STLInterval 𝕋) (t : ℝ)
    (ht : 0 ≤ t) : -- --- CONCL ---
    (PointSegmentSignal.intervalUntil (lhsInt.map STLInterval.toRealInterval)
        U.toRealInterval (rhsInt.map STLInterval.toRealInterval)).at t = true →
      ((PointSegmentSignal.intervalUntilFloat shift lhsInt U rhsInt).mapTime toReal).at t =
        true := by -- --- PROOF ---
  obtain ⟨hU', -, hf⟩ := PointSegmentSignal.intervalUntilFloat_spec shift lhsInt rhsInt U
  rw [hf t ht, ((PointSegmentSignal.intervalUntil_spec _ _ _).2 t ht)]
  rintro (⟨L', hL, R', hR, a, ha, har, hl, hu, hne⟩ | ⟨h0, R', hR, hr⟩)
  · -- the witness `a` and the until time `a - t ≠ 0` give `t` in the shift
    obtain ⟨L, hL0, rfl⟩ := List.mem_map.1 hL
    obtain ⟨R, hR0, rfl⟩ := List.mem_map.1 hR
    rw [STLInterval.set_toRealInterval] at ha hu
    rw [← STLInterval.rightClosure_toRealInterval, STLInterval.set_toRealInterval] at har
    rw [← STLInterval.leftClosure_toRealInterval, STLInterval.set_toRealInterval] at hl
    refine Or.inl ⟨L, hL0, R, hR0, hshift _ _ ⟨⟨a, ?_, a - t, ?_, by ring⟩, ht⟩, hl⟩
    · rw [STLInterval.set_and_]
      exact ⟨ha, har⟩
    · rw [hU', Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hu, fun e => hne (by linarith)⟩
  · -- the right-hand side holds at `t` itself
    obtain ⟨R, hR0, rfl⟩ := List.mem_map.1 hR
    rw [STLInterval.set_toRealInterval] at h0 hr
    exact Or.inr ⟨h0, R, hR0, hr⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
