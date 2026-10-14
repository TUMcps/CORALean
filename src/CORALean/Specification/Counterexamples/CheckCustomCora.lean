module

@[expose] public section

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

# CORA's `check` of a custom specification accepts a cell with a violating piece

For a cell `{S_ok, S_bad}` and a `func` that is `true` on `S_ok` only, `aux_checkCustom`
(`check.m`, l. 319-333) returns `true` on the first piece and exits, so `check` reports the
specification satisfied (`res = true`), while a piece violates it. The documented meaning of
`func` is that it holds of a set that satisfies the specification (`res - true/false whether
set satisfies the specification`), and the safe-set and unsafe-set helpers require every
piece. Read from the source, not run in MATLAB.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `aux_checkCustom` on a cell, as printed: `true` as soon as one piece passes `func`,
`false` for an empty cell. -/
def Specification.checkCustomCora {α : Type} (func : α → Bool) : List α → Bool
  | [] => false
  | s :: rest => if func s then true else Specification.checkCustomCora func rest


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.checkCustomCora_any_counterexample {α : Type} (func : α → Bool)
    (sOk sBad : α) (hOk : func sOk = true) (hBad : func sBad = false) :
    Specification.checkCustomCora func [sOk, sBad] = true ∧
      ¬ ∀ s ∈ [sOk, sBad], func s = true := by
  refine ⟨by simp [Specification.checkCustomCora, hOk], fun h => ?_⟩
  have := h sBad (by simp)
  rw [hBad] at this
  exact Bool.false_ne_true this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
