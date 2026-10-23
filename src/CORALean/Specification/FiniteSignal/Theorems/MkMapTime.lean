module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# The constructor at a float time type, read as reals

Over a float scalar `𝕋` the constructor's checks compare time stamps exactly (`TimeOrder`), so they
pass exactly when they pass for the reals the stamps denote: the float signal read through `toReal`
is the real constructor's signal, and both throw together.

## Inputs
* `V` – value type
* `time` – breakpoint times
* `value` – values per breakpoint

## Hypotheses
* none

## Conclusion
* the float constructor's result, read as reals, is the real constructor's
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

theorem FiniteSignal.mk?_mapTime {V : Type} [DecidableEq V] (time : List 𝕋)
    (value : List V) : -- --- CONCL ---
    (FiniteSignal.mk? time value).map (FiniteSignal.mapTime toReal) =
      FiniteSignal.mk? (time.map toReal) value := by -- --- PROOF ---
  -- the checks agree, every comparison being one of the reals
  have hiff : (time ≠ [] ∧ time.length = value.length ∧ time.Pairwise (· < ·) ∧
      value.IsChain (· ≠ ·) ∧ ∀ t ∈ time, 0 ≤ t) ↔ (time.map toReal ≠ [] ∧
      (time.map toReal).length = value.length ∧ (time.map toReal).Pairwise (· < ·) ∧
      value.IsChain (· ≠ ·) ∧ ∀ t ∈ time.map toReal, 0 ≤ t) := by
    simp only [ne_eq, List.map_eq_nil_iff, List.length_map, List.pairwise_map,
      List.forall_mem_map, le_iff_toReal_le (𝕋 := 𝕋), toReal_zero_eq (𝕋 := 𝕋)]
    rfl
  unfold FiniteSignal.mk?
  by_cases h : time ≠ [] ∧ time.length = value.length ∧ time.Pairwise (· < ·) ∧
      value.IsChain (· ≠ ·) ∧ ∀ t ∈ time, 0 ≤ t
  · rw [if_pos h, if_pos (hiff.mp h)]; rfl
  · rw [if_neg h, if_neg (mt hiff.mpr h)]; rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
