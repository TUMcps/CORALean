module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA's `levelSet/contains_` at a set, a cell of operators, as printed

CORA's `@levelSet/contains_.m` against a set `S` (l. 90-133): the guard `strcmp(ls.compOp,'==')`
(l. 93) rejects a single `'=='` only — on a cell it is a logical array, false as an `if`
condition as soon as one entry is not `'=='`. Then `I = ls.funHan(interval(S))` is the interval
evaluation of the function at the box enclosing `S` and `ub = supremum(I)`; with a cell `compOp`
each row is tested by `ub(i) < 0 | withinTol(ub(i),0)` at `'<='` (default tolerance `1e-8`; the
relative test of `withinTol` against `0` never holds) and by `ub(i) < 0` at every other
operator, `'=='` included (l. 124-128). CORALean has no interval evaluation of a real function,
so the bounds `(lb, ub)` are the argument `B`, assumed a range bound (`IsRangeBound`) by the
theorems. `ub < 0` proves the row's function nonzero on `S`, the opposite of `== 0`; kept only so
that `LevelSet.containsCellCora_counterexample` can state that it is unsound.

# CORA's `levelSet/contains_` accepts a box outside an equality constraint

For `ls = levelSet([x - 2; x - 10], x, {'==','<='})`, the set `{2}`, and `S = interval(0, 1)`,
the guard at l. 93 does not fire on the cell, the interval evaluation over `[0, 1]` is
`[-2, -1]` and `[-10, -9]`, so `ub = (-1, -9)`, and the cell branch tests the `'=='` row by
`ub(1) < 0` (l. 127), which holds: CORA answers `true`, yet `0 ∈ S` is not in `ls` (read from the
source, not run). The bounds are the exact ranges, so any range bound tighter than CORA's would
give the same verdict.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- The cell branch of `contains_(ls, S)` for a set `S`, `B i = (lb i, ub i)` the interval
evaluation of row `i` over `interval(S)`. -/
def LevelSet.containsCellCora (op : Fin m → CompOp) (B : Fin m → Interval ℝ) : Prop :=
  let ub : Fin m → ℝ := fun i => (B i).sup
  let resVec : Fin m → Prop := fun i =>
    match op i with
    | .le => ub i < 0 ∨ |ub i| ≤ 1 / 10 ^ 8
    | _ => ub i < 0
  ∀ i, resVec i

end CORALean.Real

namespace CORALean.Real

open CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.containsCellCora_counterexample : -- --- STMT ---
    let ls : LevelSet 1 := ⟨2, fun x => ![x 0 - 2, x 0 - 10], ![CompOp.eq, CompOp.le]⟩
    let S : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩
    let B : Fin 2 → Interval ℝ := ![⟨-2, -1⟩, ⟨-10, -9⟩]
    (∀ i, IsRangeBound (fun x => ls.f x i) S.construct (B i).inf (B i).sup) ∧
      LevelSet.containsCellCora ls.op B ∧ ¬ S.construct ⊆ ls.construct := by -- --- PROOF ---
  intro ls S B
  refine ⟨?_, ?_, ?_⟩
  · -- `x - 2` and `x - 10` over `[0, 1]`
    intro i x hx
    have hl : (0 : ℝ) ≤ x 0 := (hx 0).1
    have hu : x 0 ≤ 1 := (hx 0).2
    fin_cases i <;> simp [ls, B] <;> constructor <;> linarith
  · -- both upper bounds are negative
    intro i
    fin_cases i <;> simp [ls, B]
  · -- `0 ∈ [0, 1]`, and `0 - 2 ≠ 0`
    intro h
    have hmem : (fun _ => (0 : ℝ) : Vec ℝ 1) ∈ S.construct :=
      fun _ => ⟨le_rfl, zero_le_one⟩
    have := h hmem 0
    simp [ls, CompOp.holds] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
