import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Cost.MtimesIntervalMat

/-!
# `ConZonotope.mtimesIntervalMatCost`

Asserted, not proved: `Operations/MtimesIntervalMat.lean` reads the radius off
`cZ.zonotope`, a field copy, and pulls the polytope back along `blockLeft`, a
block embedding, so neither the constraints nor the conversion cost anything and
the count is `Zonotope.mtimesIntervalMatCost`'s. The bound the constraints could
tighten is not computed, which is why this is no dearer than the unconstrained
case.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.mtimesIntervalMat` costs at `IM : Interval (Mat ℝ m n)`
and `h` generators. -/
def ConZonotope.mtimesIntervalMatCost (m n h : ℕ) : Cost := Zonotope.mtimesIntervalMatCost m n h

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mtimesIntervalMatCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    ConZonotope.mtimesIntervalMatCost m n h ≤ ConZonotope.mtimesIntervalMatCost m n h' :=
  Zonotope.mtimesIntervalMatCost_mono m n hh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
