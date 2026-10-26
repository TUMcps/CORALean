module

public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.FindIntervals

@[expose] public section

/-!
# The runs of a signal with its time stamps mapped

`findIntervals` reads the breakpoints off the stored pairs and compares no time stamp, so mapping
the time stamps by an `f` that keeps `0` maps the bounds of every run: over a float scalar, the
runs of the signal read as reals are the float runs read as reals.

## Inputs
* `T` – time type
* `T'` – mapped time type
* `V` – value type
* `f` – map of the time stamps
* `s` – signal
* `cond` – condition on values

## Hypotheses
* `hf` – the map keeps `0`

## Conclusion
* the runs of the mapped signal are the mapped runs
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.findIntervals_mapTime {T T' V : Type} [Zero T] [Zero T'] (f : T → T')
    (hf : f 0 = 0) (s : FiniteSignal T V) (cond : V → Bool) : -- --- CONCL ---
    (s.mapTime f).findIntervals cond =
      (s.findIntervals cond).map fun I => ⟨f I.inf, f I.sup⟩ := by -- --- PROOF ---
  -- the loop from any start, the breakpoints mapped
  have hloop : ∀ (l : List (T × V)) (start : T),
      FiniteSignal.aux_findIntervalsLoop cond (f start) (l.map (Prod.map f id)) =
        (FiniteSignal.aux_findIntervalsLoop cond start l).map fun I => ⟨f I.inf, f I.sup⟩ := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x rest ih =>
      intro start
      obtain ⟨x1, x2⟩ := x
      rcases rest with _ | ⟨⟨y1, y2⟩, rest⟩
      · simp only [List.map_cons, List.map_nil, FiniteSignal.aux_findIntervalsLoop,
          Prod.map_apply, id_eq]
        split_ifs <;> rfl
      · -- a falling edge closes a run, a rising edge starts the next
        have ih' := ih (if (!cond x2 && cond y2) = true then x1 else start)
        simp only [List.map_cons, Prod.map_apply, id_eq] at ih' ⊢
        simp only [FiniteSignal.aux_findIntervalsLoop, List.map_append]
        rw [show (if (!cond x2 && cond y2) = true then f x1 else f start) =
          f (if (!cond x2 && cond y2) = true then x1 else start) by split_ifs <;> rfl, ih']
        split_ifs <;> rfl
  unfold FiniteSignal.findIntervals FiniteSignal.pairs FiniteSignal.mapTime
  rw [List.zip_map_left, ← hf, hloop]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
