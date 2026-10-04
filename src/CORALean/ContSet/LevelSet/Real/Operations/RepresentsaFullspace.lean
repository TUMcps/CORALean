import CORALean.ContSet.LevelSet.Real.LevelSet
import Mathlib.Data.EReal.Basic

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
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LevelSet.representsa_fullspace (L : LevelSet n) (O : Fin L.m → EReal × EReal) : Prop :=
  ∀ i, match L.op i with
    | .eq => (O i).1 = 0 ∧ (O i).2 = 0
    | .le => ¬(0 < (O i).2)
    | .lt => ¬(0 ≤ (O i).2)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
