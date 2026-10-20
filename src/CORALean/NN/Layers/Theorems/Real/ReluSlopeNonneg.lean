module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Layers.Operations.ReluSlope

@[expose] public section

/-!
# The default ReLU slope is nonnegative at ℝ

ℝ-only: the secant branch is reached only when `u ≤ 0` has been ruled out, which at ℝ the
exact order decides, and a machine `le` answering `false` rules out nothing. Elsewhere
`clampUnit` makes a slope legal instead, so no layer depends on this.

## Inputs
* `l` – lower end of the box
* `u` – upper end of the box

## Hypotheses
* none

## Conclusion
* the default ReLU slope is nonnegative
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- One case per branch of `reluSlope`, the secant's being the only one to argue. -/
theorem reluSlope_nonneg (l u : ℝ) : 0 ≤ reluSlope l u := by -- --- PROOF ---
  show 0 ≤ (if decide (u ≤ 0) = true then (0 : ℝ)
    else if decide (0 ≤ l) = true then 1 else u / (u + -l))
  split
  · exact le_rfl
  · rename_i hu
    split
    · exact zero_le_one
    · rename_i hl
      replace hu : 0 < u := not_le.mp (by simpa using hu)
      replace hl : l < 0 := not_le.mp (by simpa using hl)
      exact div_nonneg (le_of_lt hu) (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
