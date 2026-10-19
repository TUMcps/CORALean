module

public import CORALean.Specification.FiniteSignal.Operations.ValueAt
public import CORALean.Specification.FiniteSignal.Operations.At

@[expose] public section

/-!
# The index `at` reads

For arrays of one length, `at` reads the value of the first breakpoint whose time exceeds the
given one, the last if there is none: `valueAt` of the breakpoints, in the range of the signal.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `i`-th value is the one of the first breakpoint above `t`. -/
theorem aux_value_getElem_eq_valueAt {T V : Type} [LinearOrder T] (t : T) : -- --- CONCL ---
    ∀ (time : List T) (value : List V), time.length = value.length →
      value[min (time.takeWhile (· ≤ t)).length (time.length - 1)]? =
        FiniteSignal.valueAt (time.zip value) t
  | [], [], _ => by simp [FiniteSignal.valueAt]
  | [_], [v], _ => by simp [FiniteSignal.valueAt]
  | b :: x :: ts, v :: w :: ws, h => by
    have ih := aux_value_getElem_eq_valueAt t (x :: ts) (w :: ws) (by simpa using h)
    by_cases hb : b ≤ t
    · have e1 : (b :: x :: ts).takeWhile (· ≤ t) =
          b :: (x :: ts).takeWhile (· ≤ t) := by -- --- PROOF ---
        simp [List.takeWhile_cons, hb]
      rw [e1]
      simp only [List.length_cons, List.zip_cons_cons, FiniteSignal.valueAt, not_lt.mpr hb,
        if_false, Nat.add_sub_cancel] at ih ⊢
      generalize (List.takeWhile (· ≤ t) (x :: ts)).length = k at ih ⊢
      rw [show min (k + 1) (ts.length + 1) = min k ts.length + 1 by omega,
        List.getElem?_cons_succ]
      exact ih
    · simp [hb, FiniteSignal.valueAt, not_le.mp hb]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.at?_eq_valueAt {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V)
    (hl : s.time.length = s.value.length) (t : T) :
    s.at? t = if 0 ≤ t ∧ t ≤ s.duration then FiniteSignal.valueAt s.pairs t else none := by
  unfold FiniteSignal.at?
  split_ifs
  · exact aux_value_getElem_eq_valueAt t s.time s.value hl
  · rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
