module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.LevelSet
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `LevelSet.representsa_fullspace`

CORA's `@levelSet/representsa_` at `fullspace`: `O = ls.funHan(interval.Inf(n))`, the interval
evaluation of the function at the whole space, and a verdict per row from its bounds. Those
bounds can be infinite (`x²` is `[0, ∞]` there), and CORALean has no interval evaluation of a
real function, so `O i = (inf, sup)` is the argument, in `EReal`, assumed to enclose the row's
range (`Theorems/RepresentsaFullspaceSound`).
`aux_representsa_fullspace` turns `res = true` `false` when a row may fail: `==` unless `O(i)`
equals `interval(0)`, `<=` when `O.sup(i) > 0`, `<` when `O.sup(i) ≥ 0` (`isequal` at its default
tolerance `eps` in CORA, exact here).

## Inputs
* `L` – level set
* `O` – bounds of the rows over the whole space

## Output
* every row holds everywhere
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.representsa_fullspace (L : LevelSet n) (O : Fin L.m → Interval EReal) : Prop :=
  ∀ i, match L.op i with
    | .eq => (O i).inf = 0 ∧ (O i).sup = 0
    | .le => ¬(0 < (O i).sup)
    | .lt => ¬(0 ≤ (O i).sup)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
