module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.minkDiffPoint`

CORA's `@ellipsoid/minkDiff` with a numeric column subtrahend: `s = sum(S,2)` is the vector itself
and the result is `ellipsoid(E.Q, E.q - s)`, the same shape at the shifted center. The
ellipsoid-minus-ellipsoid branch (`priv_minkDiffEllipsoid`: `isBigger`, directions `L` filtered by
`isBadDir`, an intersection or union of the per-direction ellipsoids) is not formalized.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `minkDiff(E, s)` for a vector `s`: `ellipsoid(E.Q, E.q - s)`. -/
def Ellipsoid.minkDiffPoint (E : Ellipsoid n) (s : Vec ℝ n) : Ellipsoid n :=
  ⟨E.Q, E.q - s, E.psd⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
