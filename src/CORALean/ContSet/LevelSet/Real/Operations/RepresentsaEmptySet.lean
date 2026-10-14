module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.LevelSet
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `LevelSet.representsa_emptySet`

CORA's `@levelSet/representsa_` at `emptySet`: `O = ls.funHan(interval.Inf(n))`, the interval
evaluation of the function at the whole space, and a verdict per row from its bounds. Those
bounds can be infinite (`x²` is `[0, ∞]` there), and CORALean has no interval evaluation of a
real function, so `O i = (inf, sup)` is the argument, in `EReal`, assumed to enclose the row's
range (`Theorems/RepresentsaEmptySetSound`).
`aux_representsa_emptySet` starts at `res = true` and turns it `false` on the first row that may
be satisfiable: `==` when `0 ∈ O(i)`, `<=` when `O.inf(i) ≤ 0`, `<` when `O.inf(i) < 0`; so `true`
needs every row infeasible. The type `levelSet` (`true`), `probZonotope` (`false`) and the throw
for other types are not modelled.
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
