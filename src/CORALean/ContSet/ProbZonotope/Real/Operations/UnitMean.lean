import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

/-!
# The mean zonotope `[-1, 1]` with no covariance

In `ℝ¹`, centre `0`, one generator `1`, covariance `0`: the example on which CORA's `interval` and
`sup`, which read the covariance's eigen factor alone, return the point `0` (`IntervalCoraNotMem`,
`SupCoraLt`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.unitMean : ProbZonotope 1 := ⟨⟨1, fun _ => 0, fun _ _ => 1⟩, 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
