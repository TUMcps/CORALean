module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compactGens`

Equal exponent columns added together and the zero generators gone. The whole
constraint block stands, `p` included, so the constraint is untouched.
Noncomputable for that reason: dropping a zero column decides whether an
element of an arbitrary real module is zero.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together and the zero generators gone. The
whole constraint block stands, `p` included, so the constraint is untouched. -/
noncomputable def ConPolyZono.compactGens (cPZ : ConPolyZono α) : ConPolyZono α where
  p := cPZ.p
  h := (PolyZonotope.compactKeep cPZ.E cPZ.G).card
  qI := cPZ.qI
  c := cPZ.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep cPZ.E) cPZ.G
                  (PolyZonotope.compactIdx cPZ.E cPZ.G j)
  E := fun k j => cPZ.E k (PolyZonotope.compactIdx cPZ.E cPZ.G j)
  GI := cPZ.GI
  cons := cPZ.cons
  cons_eq := cPZ.cons_eq
  cons_dom := cPZ.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
