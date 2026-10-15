module

public import CORALean.HybridDynamics.Operations.Jump
public import CORALean.HybridDynamics.Operations.JumpOfPoint
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Transition.jumpCost`

Asserted, not proved: `Operations/Jump.lean` is `plus (mtimes e.W Rg) (embed w)`
— one `mtimes`, one `plus`, one embedding of the offset — and
`Operations/JumpOfPoint.lean` is the same three calls through `OfPoint` in
place of `OfInterval`, so one count prices either.

What `mtimes`, `plus` and the embedding cost are parameters, as in
`Layer.linear`'s own reading: `S` is abstract here, so no representation-agnostic
file can price `Zonotope.mtimesCost` against `ConPolyZono.mtimesCost`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Transition.jump` and `Transition.jumpOfPoint` cost, at what `mtimes`,
`plus` and embedding the offset cost: the three added. -/
def Transition.jumpCost (cMtimes cPlus cEmbed : Cost) : Cost := cMtimes + cPlus + cEmbed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
