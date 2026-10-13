import CORALean.Specification.Operations.CheckCustomCora

/-!
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
