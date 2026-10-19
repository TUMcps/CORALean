module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.LevelSet
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `LevelSet.representsa_emptySet`

CORA's `@levelSet/representsa_` at `emptySet`: `O = ls.funHan(interval.Inf(n))`, the interval
evaluation of the function at the whole space, and a verdict per row from its bounds. Those bounds
can be infinite (`x²` is `[0, ∞]` there), and there is no interval evaluation of a real function
here, so `O i = (inf, sup)` is the argument, in `EReal`, assumed to enclose the row's range. A row
may be satisfiable when `==` and `0 ∈ O(i)`, `<=` and `O.inf(i) ≤ 0`, or `<` and `O.inf(i) < 0`;
`true` needs every row infeasible. The types `levelSet` (`true`), `probZonotope` (`false`) and the
throw for other types are not modelled.

## Inputs
* `L` – level set
* `O` – bounds of the rows over the whole space

## Output
* every row is infeasible
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.representsa_emptySet (L : LevelSet n) (O : Fin L.m → Interval EReal) : Prop :=
  ∀ i, match L.op i with
    | .eq => ¬((O i).inf ≤ 0 ∧ 0 ≤ (O i).sup)
    | .le => ¬((O i).inf ≤ 0)
    | .lt => ¬((O i).inf < 0)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
