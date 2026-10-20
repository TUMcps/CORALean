module

public import CORALean.ContSet.Interval.Real.Operations.BoundaryRatio

@[expose] public section

/-!
# `Interval.boundaryPoint`

CORA's `@interval/boundaryPoint.m` in the bounded case: `x = dir * ratio + startPoint`, where
`ratio` is `Interval.boundaryRatio`. The farthest point of the ray from `startPoint` along `dir`
that stays in `I`; `Interval.boundaryRatio_isGreatest` says so.

## Inputs
* `I` – interval box
* `dir` – ray direction
* `start` – ray start point

## Hypotheses
* `hdir` – direction nonzero

## Output
* point where the ray leaves the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `boundaryPoint(I, dir, startPoint)`, bounded case, `dir ≠ 0`. -/
noncomputable def Interval.boundaryPoint (I : Interval (Vec ℝ n)) (dir start : Vec ℝ n)
    (hdir : ∃ i, dir i ≠ 0) : Vec ℝ n :=
  Interval.boundaryRatio I dir start hdir • dir + start

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
