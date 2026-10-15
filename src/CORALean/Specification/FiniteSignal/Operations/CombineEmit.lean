module

public import CORALean.Specification.FiniteSignal.FiniteSignal

@[expose] public section

/-!
# One step of `combine`

The end of an iteration of the loop of `combine.m`: `val(k)` and `tim(k)` are set, and `k`
advances only if both signals have a next breakpoint and the combined value there differs;
otherwise the entry is overwritten by the next iteration, or is the last one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The breakpoints the loop yields after setting `(t,v)`, given the remaining breakpoints `ls`
and `rs` and what the loop yields for them. -/
def FiniteSignal.combineEmit {T V W : Type} [DecidableEq W] (op : V → V → W) (t : T) (v : W)
    (ls rs : List (T × V)) (rest : List (T × W)) : List (T × W) :=
  match ls, rs with
  -- check if value changes in next step
  | l' :: _, r' :: _ => if v ≠ op l'.2 r'.2 then (t, v) :: rest else rest
  | _, _ => [(t, v)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
