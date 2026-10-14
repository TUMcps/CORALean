module

@[expose] public section

/-!
# `Location.jumpTimeMinCora`: the jump time in CORA's `location/reach`

In `@location/reach.m`, inside `for i = 1:size(R,1)` (the rows of the reach set, several when the
sets are split), the time of a jump is `tMin = infimum(R.timeInterval.time{minInd(j)})`
(l. 76-79, and `R.timePoint.time{..}` in the time-point case), with `R` for `R(i)` as everywhere
else in the loop. For `size(R,1) > 1` `R.timeInterval` is a comma-separated list and the
indexing `.time{..}` is a MATLAB error.

Modelled for the time-interval case: a row is the list of the infima of its time intervals; the
result is `none` for the MATLAB error. The intended value is that of `R(i)`. Read from the source,
not run.

# CORA's `location/reach` errors when a split location hits a guard

With two rows in `R` (a split reach set) and a guard met by the first row, the jump time of
`R.timeInterval.time{minInd(j)}` is a MATLAB error, where the time is that of row 1. Read from
`reach.m` l. 76-79, not run (`FINDINGS.md`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `tMin = infimum(R.timeInterval.time{m})`: defined for one row only, whatever `i`. -/
def Location.jumpTimeMinCora {α : Type} (R : List (List α)) (_i m : Nat) : Option α :=
  match R with
  | [row] => row[m]?
  | _ => none


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two rows: CORA gives no jump time for row 0, whose first infimum is `t`; with one row it
reads that row. -/
theorem Location.jumpTimeMinCora_crash {α : Type} (t : α) (rest r₂ : List α) :
    Location.jumpTimeMinCora [t :: rest, r₂] 0 0 = none ∧
      Location.jumpTimeMinCora [t :: rest] 0 0 = some t := by
  simp [Location.jumpTimeMinCora]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
