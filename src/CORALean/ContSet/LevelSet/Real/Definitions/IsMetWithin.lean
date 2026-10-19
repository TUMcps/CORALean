module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# A comparison met to within a slack

`v ⋈ 0` widened by `e ≥ 0`: `v ≤ e`, `v < e`, or `|v| ≤ e` for an equation. It is what a row of a
float polynomial level set holds once its rounding is recorded as the slack `e = |b_errorᵢ|`
(`Float.PolyLevelSet.construct`), and at `e = 0` it is `holds`.

## Inputs
* none

## Output
* the comparison of the value with `0` holds within the slack
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `v` compared with `0`, to within `e`. -/
def CompOp.IsMetWithin : CompOp → ℝ → ℝ → Prop
  | .le, v, e => v ≤ e
  | .lt, v, e => v < e
  | .eq, v, e => |v| ≤ e

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
