module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# `ConPolyZono.map`

A linear map applies to the center and to both generator blocks and touches nothing else, above
all not the constraints. That is the whole content of the file: the constraints live on the
factors, and a map of the ambient space does not move a factor, so the set of admissible factor
vectors is the same before and after. Exactness follows as for a polynomial zonotope.

## Inputs
* `f` – linear map
* `cPZ` – constrained polynomial zonotope

## Output
* image under the linear map
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.map (f : α →ₗ[ℝ] β) (cPZ : ConPolyZono α) : ConPolyZono β where
  p := cPZ.p
  h := cPZ.h
  qI := cPZ.qI
  c := f cPZ.c
  G := fun i => f (cPZ.G i)
  E := cPZ.E
  GI := fun j => f (cPZ.GI j)
  cons := cPZ.cons
  cons_eq := cPZ.cons_eq
  cons_dom := cPZ.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
