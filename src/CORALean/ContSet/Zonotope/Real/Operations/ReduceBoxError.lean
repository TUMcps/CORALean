module

public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `ε_S`: the error a reduction to a given order pays

[1]'s `ε_S([t_i,t_{i+1}])`: `err(·)` — the Euclidean radius of the box
over-approximation, [1, Prop. 1] — at the very box `reduceBox` absorbs the
dropped generators into. `adaptSetOrder` and `autoTuneSetOrder` both read it
off the same box, so it is named once here rather than folded into either.

## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* error of the absorbing box

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1]`'s `ε_S([t_i,t_{i+1}])`: `err(·)` at the box a reduction to order `o`
absorbs the generators it drops into. -/
noncomputable def Zonotope.reduceBoxError (Z : Zonotope (Vec ℝ n)) (o : ℕ) : ℝ :=
  ‖fun j => (Z.reduceBox o).absBound j‖₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
