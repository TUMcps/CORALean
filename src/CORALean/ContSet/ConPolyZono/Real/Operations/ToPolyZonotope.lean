module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.toPolyZonotope`

The generator data on its own, the constraint system left behind: CORA's
`polyZonotope(cPZ.c,cPZ.G,cPZ.GI,cPZ.E,cPZ.id)`, which every `conPolyZono`
operation that has a polynomial-zonotope counterpart starts by building.

It is not a set-level operation and no theorem here reads it as one. What it is
for is arithmetic: an operation applies a `PolyZonotope` one to the generators,
then states the constraints it assembles itself over the same factors — the
sharing the representation is built on, used in the one direction that keeps it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generator data on its own, the constraint system left behind. -/
def ConPolyZono.toPolyZonotope (cPZ : ConPolyZono α) : PolyZonotope α where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
