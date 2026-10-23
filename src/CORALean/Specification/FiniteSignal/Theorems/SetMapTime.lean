module

public import CORALean.Specification.FiniteSignal.Operations.Set
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime

@[expose] public section

/-!
# Setting a value on a float signal, read as reals

Over a float scalar `𝕋` `set` clips the bounds, finds the breakpoints around them and tests the
boundaries by exact comparisons (`TimeOrder`), so the float result read through `toReal` is `set` of
the real signal on the reals the bounds denote, and both throw together.

## Inputs
* `V` – value type
* `s` – signal
* `lo` – interval lower bound
* `hi` – interval upper bound
* `value` – value to set

## Hypotheses
* none

## Conclusion
* the float result, read as reals, is the real one
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The lower boundary of `set` is found at the same index, its new time stamp mapped. -/
theorem aux_setLower_mapTime {V : Type} [DecidableEq V] (s : FiniteSignal 𝕋 V) (a : 𝕋) (value : V)
    (k : ℕ) : -- --- CONCL ---
    (s.mapTime toReal).aux_setLower (toReal a) value k =
      ((s.aux_setLower a value k).1, (s.aux_setLower a value k).2.1.map toReal,
        (s.aux_setLower a value k).2.2) := by -- --- PROOF ---
  -- the two tests compare the reals the stamps denote
  have h0 : ∀ x : 𝕋, (0 < x) ↔ (0 < toReal x) := fun x => by
    rw [show (0 < x) ↔ toReal (0 : 𝕋) < toReal x from Iff.rfl, toReal_zero_eq]
  have he : (∃ b ∈ (s.time.map toReal)[k - 1]?, TimeOrder.Eqv b (toReal a)) ↔
      (∃ b ∈ s.time[k - 1]?, TimeOrder.Eqv b a) := by
    rw [List.getElem?_map]
    cases s.time[k - 1]? <;>
      simp [show ∀ b : 𝕋, TimeOrder.Eqv b a ↔ toReal b = toReal a from fun _ => Iff.rfl]
  unfold FiniteSignal.aux_setLower FiniteSignal.mapTime
  simp only [← h0, he]
  split_ifs <;> simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.set?_mapTime {V : Type} [DecidableEq V] (s : FiniteSignal 𝕋 V) (lo hi : 𝕋)
    (value : V) : -- --- CONCL ---
    (s.set? lo hi value).map (FiniteSignal.mapTime toReal) =
      (s.mapTime toReal).set? (toReal lo) (toReal hi) value := by -- --- PROOF ---
  -- the clipped bounds, the indices and the flag agree
  have hd : (s.mapTime toReal).duration = toReal s.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq s
  have hlb : (if toReal lo ≤ 0 then 0 else toReal lo) = toReal (if lo ≤ 0 then 0 else lo) := by
    by_cases h : lo ≤ 0
    · rw [if_pos (show toReal lo ≤ 0 by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact h), if_pos h,
        toReal_zero_eq]
    · rw [if_neg (show ¬ toReal lo ≤ 0 by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact h), if_neg h]
  -- the clipped upper bound is the float one read as reals
  have hub : (if toReal hi ≤ (s.mapTime toReal).duration then toReal hi else
      (s.mapTime toReal).duration) = toReal (if hi ≤ s.duration then hi else s.duration) := by
    rw [hd]
    by_cases h : hi ≤ s.duration
    · rw [if_pos (show toReal hi ≤ toReal s.duration from h), if_pos h]
    · rw [if_neg (show ¬ toReal hi ≤ toReal s.duration from h), if_neg h]
  -- the breakpoints up to a bound are as many
  have htw : ∀ b : 𝕋, ((s.mapTime toReal).time.takeWhile (· ≤ toReal b)).length =
      (s.time.takeWhile (· ≤ b)).length := fun b => by
    rw [FiniteSignal.mapTime, List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.time)
      (funext fun t => decide_eq_decide.mpr Iff.rfl))
  -- unfold `set` on both sides, with the bounds named
  unfold FiniteSignal.set?
  simp only [hlb, hub]
  generalize (if lo ≤ 0 then 0 else lo) = lb
  generalize (if hi ≤ s.duration then hi else s.duration) = ub
  simp only [htw, aux_setLower_mapTime]
  have hv : (s.mapTime toReal).value = s.value := rfl
  have ht : (s.mapTime toReal).time = s.time.map toReal := rfl
  rw [hv, ht, hd]
  by_cases hlu : lb < ub
  · -- a proper interval: the same lists, read as reals
    rw [if_neg (not_not.mpr hlu), if_neg (not_not.mpr (show toReal lb < toReal ub from hlu))]
    generalize s.aux_setLower lb value (List.takeWhile (fun x => decide (x ≤ lb)) s.time).length = L
    generalize (List.takeWhile (fun x => decide (x ≤ ub)) s.time).length = k
    by_cases hu : TimeOrder.Eqv ub s.duration ∨ s.value[k]? ≠ some value
    · rw [if_pos hu, if_pos hu, if_pos (show TimeOrder.Eqv (toReal ub) (toReal s.duration) ∨
        s.value[k]? ≠ some value from hu), if_pos (show TimeOrder.Eqv (toReal ub)
        (toReal s.duration) ∨ s.value[k]? ≠ some value from hu), FiniteSignal.mk?_mapTime]
      simp [List.map_take, List.map_drop]
    · rw [if_neg hu, if_neg hu, if_neg (show ¬ (TimeOrder.Eqv (toReal ub) (toReal s.duration) ∨
        s.value[k]? ≠ some value) from hu), if_neg (show ¬ (TimeOrder.Eqv (toReal ub)
        (toReal s.duration) ∨ s.value[k]? ≠ some value) from hu), FiniteSignal.mk?_mapTime]
      simp [List.map_take, List.map_drop]
  · -- an empty or singleton interval throws on both sides
    rw [if_pos hlu, if_pos (show ¬ toReal lb < toReal ub from hlu)]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
