import CORALean.HybridDynamics.Cost.Jump
import CORALean.HybridDynamics.Operations.JumpIntersection
import CORALean.HybridDynamics.Operations.JumpIntersectionOfPoint

/-!
# `Transition.jumpIntersectionCost`

Asserted, not proved: `Operations/JumpIntersection.lean` is `jump` after
`Intersection.intersection` cuts the incoming set to the guard, and
`JumpIntersectionOfPoint.lean` is `jumpOfPoint` after the same cut — one count
prices either, `cIntersection` bounding whichever `intersection` the caller
runs.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Transition.jumpIntersection` and `Transition.jumpIntersectionOfPoint`
cost: the guard cut, then `jumpCost`. -/
def Transition.jumpIntersectionCost (cIntersection cMtimes cPlus cEmbed : Cost) : Cost :=
  cIntersection + Transition.jumpCost cMtimes cPlus cEmbed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
