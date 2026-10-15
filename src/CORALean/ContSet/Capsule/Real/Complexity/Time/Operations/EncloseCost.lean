module

public import CORALean.ContSet.Capsule.Real.Operations.Enclose
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.ConvHullCost

@[expose] public section

/-!
# `Capsule.encloseCost`

Asserted, not proved: `Operations/Enclose.lean` is `Capsule.mtimes M Cplus`
followed by `convHull` of the result with `C`, so the two costs add.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.enclose` costs at `M : Mat ℝ n m`, a capsule in `Vec ℝ n`. -/
def Capsule.encloseCost (n m : ℕ) : Cost := Capsule.mtimesCost n m + Capsule.convHullCost n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
