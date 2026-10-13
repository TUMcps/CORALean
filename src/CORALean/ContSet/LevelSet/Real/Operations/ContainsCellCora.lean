import CORALean.ContSet.LevelSet.Real.LevelSet

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
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cell branch of `contains_(ls, S)` for a set `S`, `B i = (lb i, ub i)` the interval
evaluation of row `i` over `interval(S)`. -/
def LevelSet.containsCellCora (op : Fin m → CompOp) (B : Fin m → ℝ × ℝ) : Prop :=
  let ub : Fin m → ℝ := fun i => (B i).2
  let resVec : Fin m → Prop := fun i =>
    match op i with
    | .le => ub i < 0 ∨ |ub i| ≤ 1 / 10 ^ 8
    | _ => ub i < 0
  ∀ i, resVec i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
