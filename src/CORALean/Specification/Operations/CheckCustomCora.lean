/-!
# `checkCustomCora`, CORA's `check` of a `'custom'` specification on a cell of sets

CORA's `aux_checkCustom(func, S)` (`specification/@specification/check.m`, l. 319-333) for a
cell `S`, which `check` is given by `reach` for the parallel sets of a step
(`contDynamics/@contDynamics/reach.m`, l. 152, 197, `check(spec, Rnext.ti, ...)`): `res =
false`, then for each piece `res = func(S{i})` and an early exit as soon as `res` is `true`
(l. 322-327). `func` returns `true` for a set that satisfies the specification (`check`
returns `res` and reports a violation when `~res`, l. 261-266), and the sibling helpers
`aux_checkSafeSet` and `aux_checkUnsafeSet` run through the cell with the exit on `~res`, so
that every piece must pass. The loop is recursion on the cell. Pieces are any type `α`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_checkCustom` on a cell, as printed: `true` as soon as one piece passes `func`,
`false` for an empty cell. -/
def Specification.checkCustomCora {α : Type} (func : α → Bool) : List α → Bool
  | [] => false
  | s :: rest => if func s then true else Specification.checkCustomCora func rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
