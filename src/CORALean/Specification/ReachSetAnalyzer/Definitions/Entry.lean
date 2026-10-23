module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.TimedSet

@[expose] public section

/-!
# An entry of a reach set

What `reachSetAnalyzer` reads of one element `R(i)` of an array of CORA `reachSet`s: the index of
its parent (`0` for the initial one), its location, and its `timeInterval`: the sets with the time
interval `[lo,hi]` each is reachable in (`TimedSet`). The `timePoint` sets are not read. A
`zonoBundle` set is converted to a zonotope first (`analyzeSingle`), which is a change of the
representation `S`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- One element of an array of reach sets: the index of its parent, its location, and its sets with
the time intervals they are reachable in. -/
structure ReachSetAnalyzer.Entry (T : Type) (S : ℕ → Type) (n : ℕ) where
  parent : ℕ
  loc : ℕ
  timeInterval : List (ReachSetAnalyzer.TimedSet T S n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
