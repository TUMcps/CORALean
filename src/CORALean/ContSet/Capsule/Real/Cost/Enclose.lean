import CORALean.ContSet.Capsule.Real.Operations.Enclose
import CORALean.ContSet.Capsule.Real.Cost.Mtimes
import CORALean.ContSet.Capsule.Real.Cost.ConvHull

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

/-- Monotone in both dimensions. -/
theorem Capsule.encloseCost_mono {n n' m m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    Capsule.encloseCost n m ≤ Capsule.encloseCost n' m' :=
  Cost.add_le_add (Capsule.mtimesCost_mono hn hm) (Capsule.convHullCost_mono hn)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
