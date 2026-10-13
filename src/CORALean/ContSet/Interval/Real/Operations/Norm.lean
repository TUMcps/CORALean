module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Interval.norm`

CORA's `@interval/norm_` at `type = 2`: the Euclidean norm of the entrywise larger of `|inf|` and
`|sup|`. CORA answers `-Inf` for an interval whose bounds are empty arrays, which has no
counterpart here: a box over `Vec ℝ 0` denotes the point, not `∅`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval/norm_` for `type = 2`. -/
noncomputable def Interval.norm (I : Interval (Vec ℝ n)) : ℝ :=
  ‖(fun i => max |I.inf i| |I.sup i|)‖₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
