module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together and the zero columns gone.
`b` stands: a merged column is exact, and a column at exponent zero stays a
column here rather than moving into the bound.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal constraint exponent columns added together and the zero columns gone.
`b` stands: a merged column is exact, and a column at exponent zero stays a
column here rather than moving into the bound. -/
noncomputable def ConPolyZono.compactCons (cPZ : ConPolyZono α) : ConPolyZono α where
  p := cPZ.p
  h := cPZ.h
  qI := cPZ.qI
  m := cPZ.m
  q := (PolyZonotope.compactKeep cPZ.R (ConPolyZono.consCol cPZ.A)).card
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI
  A := fun i l => PolyZonotope.fiberSum (PolyZonotope.rep cPZ.R) (ConPolyZono.consCol cPZ.A)
                    (PolyZonotope.compactIdx cPZ.R (ConPolyZono.consCol cPZ.A) l) i
  b := cPZ.b
  R := fun k l => cPZ.R k (PolyZonotope.compactIdx cPZ.R (ConPolyZono.consCol cPZ.A) l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
