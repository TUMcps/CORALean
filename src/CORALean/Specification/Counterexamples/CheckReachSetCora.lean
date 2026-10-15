module

@[expose] public section

/-!
# `checkReachSetCora`, CORA's `check` of a specification on a `reachSet`

The `reachSet` branch of `specification/@specification/check.m` (l. 126-168) runs, for each row
`k` of `S`, `timeInterval = S(k).timeInterval;` and `for j = 1:length(timeInterval.set)`, and for
a specification without time checks `timeInterval.set{j}`. A `reachSet` made by
`reachSet(timePoint)` has `timeInterval = []` (`reachSet.m` l. 44, 79-80), a `double`, and
`timeInterval.set` on it is a MATLAB error. The discrete-time systems return exactly that
(`linearSysDT/reach.m` l. 133, 157, `nonlinearSysDT/reach.m` l. 90, 99).

Modelled for one row and a specification without time: `timeInterval` is `none` for `[]` and
`some sets` for a struct with its list of sets; `ok` is `check` on one set. The result is `none`
for the MATLAB error. Read from the source, not run.

# CORA's `check` errors on the reach set of a discrete-time system

`check(spec, R)` for `R = reach(linsysDT, ...)` (or `nonlinearSysDT`) reads `R(k).timeInterval.set`
of `timeInterval = []` and errors, whatever the specification and the sets, although the
`timePoint` sets are there to check. Read from `check.m` l. 143-148, not run
(`references/coverage/specification/specification.md`, row `check`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `check` of an untimed specification on one row of a `reachSet`, as printed: it reads
`timeInterval.set`, an error (`none`) for `timeInterval = []`. -/
def Specification.checkReachRowCora {α : Type} (ok : α → Bool) :
    Option (List α) → Option Bool
  | none => none
  | some sets => some (sets.all ok)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A row with no time intervals gives the MATLAB error for every `ok`, a row with time intervals
does not. -/
theorem Specification.checkReachRowCora_crash {α : Type} (ok : α → Bool) :
    Specification.checkReachRowCora ok none = none ∧
      Specification.checkReachRowCora ok (some []) = some true := by
  simp [Specification.checkReachRowCora]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
