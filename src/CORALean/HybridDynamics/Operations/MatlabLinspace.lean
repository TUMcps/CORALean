import Mathlib.Algebra.Field.Basic

/-!
# MATLAB's `linspace(a, b, n)`

The list of the `n` points MATLAB's `linspace(a, b, n)` returns: empty for `n = 0`, `[b]` for
`n = 1` (MATLAB returns the upper end), otherwise `a + k (b - a) / (n - 1)` for `k < n`.
Used to read the time grids of the `simulateRandom` methods.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The points of `linspace(a, b, n)`. -/
def matlabLinspace {α : Type} [Field α] (a b : α) (n : Nat) : List α :=
  if n = 0 then [] else if n = 1 then [b]
  else (List.range n).map fun (k : Nat) => a + (k : α) * (b - a) / ((n : α) - 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
