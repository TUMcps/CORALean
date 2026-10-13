module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# `ConPolyZono.map`

A linear map applies to the centre and to both generator blocks and touches
nothing else — not the exponent matrix, not the counts, and above all not the
constraints.

That last part is the whole content of the file. The constraints live on the
factors, and a map of the ambient space does not move a factor, so the set of
admissible factor vectors is the same before and after. Exactness follows for
the same reason it does for a polynomial zonotope: the same witnesses work in
both directions.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.map (f : α →ₗ[ℝ] β) (cPZ : ConPolyZono α) : ConPolyZono β where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := f cPZ.c
  G := fun i => f (cPZ.G i)
  E := cPZ.E
  GI := fun j => f (cPZ.GI j)
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
