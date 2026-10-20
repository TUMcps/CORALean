module

public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.CellsFrom

@[expose] public section

/-!
# The cells by index

The `m`-th cell of breakpoints after `a` is `[a, time(0)]` for `m = 0`, else `[time(m-1),
time(m)]`, with the value of the `m`-th breakpoint; there is one cell per breakpoint.

## Inputs
* `T` – time type
* `V` – value type
* `c` – cell

## Hypotheses
* none

## Conclusion
* the cell is the cell of some breakpoint index
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.mem_cellsFrom_iff {T V : Type} (c : (T × T) × V) :
    ∀ (a : T) (L : List (T × V)), c ∈ FiniteSignal.cellsFrom a L ↔
      ∃ (m : ℕ) (h : m < L.length), c = ((if m = 0 then a else (L[m - 1]'(by omega)).1,
        L[m].1), L[m].2)
  | _, [] => by simp [FiniteSignal.cellsFrom]
  | a, (b, v) :: rest => by
    rw [FiniteSignal.cellsFrom, List.mem_cons, FiniteSignal.mem_cellsFrom_iff c b rest]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · refine ⟨m + 1, by simpa using hm, ?_⟩
        cases m with
        | zero => simp
        | succ m => simp
    · rintro ⟨m, hm, rfl⟩
      cases m with
      | zero => exact Or.inl (by simp)
      | succ m =>
        refine Or.inr ⟨m, by simpa using hm, ?_⟩
        cases m with
        | zero => simp
        | succ m => simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
