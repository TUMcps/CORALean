import Mathlib.Algebra.Group.Defs

/-!
# A Newton iteration run to a stopping test

The loop of CORA's `consistentInitialState` and `steadyState`: compute the step `Δ = step y`, test
it, and move to `y + Δ`, the test passing or not. When the test passes the iteration stops *after*
the move, so the returned point is one step beyond the iterate the test was made on.

CORA loops until the test passes, with no bound; this one takes a `fuel` and gives `none` when it
runs out. Computable: the step and the test are parameters.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Iterate `y ↦ y + step y` from `y₀`, returning the point reached by the first step that
`small` accepts, or `none` after `fuel` steps without one. -/
def newtonIterate {V : Type} [Add V] (step : V → V) (small : V → Bool) : ℕ → V → Option V
  | 0, _ => none
  | fuel + 1, y =>
    if small (step y) then some (y + step y) else newtonIterate step small fuel (y + step y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
