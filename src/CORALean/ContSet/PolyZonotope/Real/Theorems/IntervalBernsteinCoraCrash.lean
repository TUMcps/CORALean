module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IntervalBernsteinCora

@[expose] public section

/-!
# CORA's `interval(pZ, 'bernstein')` errors for a one-dimensional polynomial zonotope

`poly2bernstein` returns a matrix, not a cell, when the dimension is `1`, and
`@polyZonotope/interval.m` l. 71 applies `cellfun` to it. The set has a bounding interval all
the same. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every one-dimensional `pZ` with a dependent generator and a factor makes CORA error. -/
theorem PolyZonotope.interval_bernstein_cora_crash (pZ : PolyZonotope (Vec ℝ 1))
    (hh : 0 < pZ.h) (hp : 0 < pZ.p) : pZ.intervalBernsteinCora = none := by
  simp [PolyZonotope.intervalBernsteinCora, hh, hp]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
