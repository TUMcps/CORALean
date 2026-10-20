import Mathlib.Data.Rat.Defs

/-!
# `randverify`: the signed distance to an unsafe box

For one window with output hull `H` and an unsafe box `S`, the gap in dimension `i` is
`max (H_i.inf - S_i.sup) (S_i.inf - H_i.sup)`: positive iff `H` and `S` are separated there, and
`H ∩ S = ∅` as soon as one dimension's gap is positive. The window's distance is the largest gap
over the dimensions, the set's the smallest such over the windows: positive iff every window is
separated from `S`. Exact, over ℚ.

## Inputs
* `hulls` – output hulls of the windows
* `S` – unsafe box

## Output
* signed distance to the box, none if no window
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The largest gap of `H` from `S` over the dimensions. -/
def aux_windowGap (H S : Array (ℚ × ℚ)) : Option ℚ :=
  (H.zip S).foldl (fun acc ((hl, hh), (sl, sh)) =>
    let g := max (hl - sh) (sl - hh)
    some (acc.elim g (max g))) none


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `none` if there is no window or no dimension. -/
def signedDistance (hulls : List (Array (ℚ × ℚ))) (S : Array (ℚ × ℚ)) : Option ℚ :=
  hulls.foldl (fun acc H => match aux_windowGap H S with
    | none => acc
    | some g => some (acc.elim g (min g))) none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
