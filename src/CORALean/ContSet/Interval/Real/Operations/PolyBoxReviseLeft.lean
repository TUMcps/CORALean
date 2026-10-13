import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Real.Basic

/-!
# `Interval.polyBoxReviseLeft`

[1, Sec. 3 (three cases)]: the new left bound of `[x] = [x̲, x̅]` from the extremal functions
`g̲ ≤ g̅`. Three cases: `g̲(x̲) ≤ 0 ≤ g̅(x̲)` keeps `x̲`; `g̲(x̲) > 0` selects `g̲`, `g̅(x̲) < 0`
selects `g̅`, and the bound becomes the smallest root of the selected function in `[x]`, which
`BoxNarrow` or a closed form computes. That search is the argument `root`; what it has to
guarantee is `Interval.IsLeftRootBound`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The left bound `l` of `[x̲, x̅]` the three cases give. -/
noncomputable def Interval.polyBoxReviseLeft (gLo gHi : ℝ → ℝ) (root : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (xl xu : ℝ) : ℝ :=
  if gLo xl ≤ 0 ∧ 0 ≤ gHi xl then xl                -- 1. no contraction
  else if 0 < gLo xl then root gLo xl xu            -- 2. `g̲` selected
  else root gHi xl xu                               -- 3. `g̅(x̲) < 0`: `g̅` selected

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
