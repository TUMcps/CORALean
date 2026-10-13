import CORALean.ContSet.LevelSet.Real.Operations.ContainsCellCora
import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
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
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.containsCellCora_counterexample :
    let ls : LevelSet 1 := ⟨2, fun x => ![x 0 - 2, x 0 - 10], ![CompOp.eq, CompOp.le]⟩
    let S : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩
    let B : Fin 2 → ℝ × ℝ := ![(-2, -1), (-10, -9)]
    (∀ i, IsRangeBound (fun x => ls.f x i) S.construct (B i).1 (B i).2) ∧
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
