module

public import CORALean.Specification.FiniteSignal.Operations.ValueAt

@[expose] public section

/-!
# The value past the first breakpoint

Past the first breakpoint, the value held is that of the others (if there are any).

## Inputs
* `T` – time type
* `V` – value type
* `p` – first breakpoint
* `q` – remaining breakpoints
* `t` – time

## Hypotheses
* `h` – the time is not before the first breakpoint
* `hq` – there are further breakpoints

## Conclusion
* the value is that of the remaining breakpoints
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Past the first breakpoint, the value is that of the others (if there are any). -/
theorem FiniteSignal.valueAt_cons_of_ge {T V : Type} [LinearOrder T] (p : T × V) (q : List (T × V))
    (t : T) (h : ¬ t < p.1) (hq : q ≠ []) : -- --- CONCL ---
    FiniteSignal.valueAt (p :: q) t =
      FiniteSignal.valueAt q t := by -- --- PROOF ---
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hq
  obtain ⟨b, v⟩ := p
  obtain ⟨x1, x2⟩ := x
  have h' : ¬ t < b := h
  simp [FiniteSignal.valueAt, h']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
