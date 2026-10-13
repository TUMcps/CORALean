import CORALean.ContSet.SpectraShadow.Real.Operations.ConvHull

/-!
# `SpectraShadow.or`

CORA's `or(SpS, S)` of a spectrahedral shadow: `S_out = convHull_(SpS, S, varargin{:})`, the
convex hull of the union. A shadow is convex, so the union is closed under nothing smaller.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.or (SpS S : SpectraShadow (Vec ℝ n)) : SpectraShadow (Vec ℝ n) :=
  SpS.convHull_ S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
