module

public import CORALean.Global.Cost
public import CORALean.HybridDynamics.Operations.Jump
public import CORALean.HybridDynamics.Operations.JumpIntersection
public import CORALean.HybridDynamics.Operations.JumpIntersectionOfPoint
public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.ContSet.ContSet
public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# `Transition.jumpIntersectionCost`

Asserted, not proved: `Operations/JumpIntersection.lean` is `jump` after
`Intersection.intersection` cuts the incoming set to the guard, and
`JumpIntersectionOfPoint.lean` is `jumpOfPoint` after the same cut — one count
prices either, `cIntersection` bounding whichever `intersection` the caller
runs.

## Inputs
* `cIntersection` – cost of the intersection
* `cMtimes` – cost of the matrix product
* `cPlus` – cost of the Minkowski sum
* `cEmbed` – cost of the embedding

## Output
* cost of a jump through an intersection guard
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What `Transition.jump` and `Transition.jumpOfPoint` cost, at what `mtimes`,
`plus` and embedding the offset cost: the three added. -/
def Transition.aux_jumpCost (cMtimes cPlus cEmbed : Cost) : Cost := cMtimes + cPlus + cEmbed


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Transition.jumpIntersection` and `Transition.jumpIntersectionOfPoint`
cost: the guard cut, then `aux_jumpCost`. -/
def Transition.jumpIntersectionCost (cIntersection cMtimes cPlus cEmbed : Cost) : Cost :=
  cIntersection + Transition.aux_jumpCost cMtimes cPlus cEmbed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
