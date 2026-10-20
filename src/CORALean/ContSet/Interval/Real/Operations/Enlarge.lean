module

public import CORALean.ContSet.Interval.Real.Operations.IntervalMatrix

@[expose] public section

/-!
# `Interval.enlarge`

CORA's `@interval/enlarge`: scale the half-width about the center, `[c - f·r, c + f·r]`. CORA takes
a scalar or entrywise factor; this is the scalar one. CORA's infinite half-widths (`Inf` stays `Inf`
for a factor above one, and a factor below one is an error) have no counterpart: a box over ℝ has
finite bounds.

## Inputs
* `I` – interval
* `f` – enlargement factor

## Output
* interval enlarged about its center by factor `f`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.enlarge (I : Interval α) (f : ℝ) : Interval α :=
  Interval.ofCenterRadius I.center (f • I.radius)
end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
