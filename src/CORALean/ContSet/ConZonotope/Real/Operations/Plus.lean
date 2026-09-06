import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.plus`

CORA's `@conZonotope/plus`: centres add and generators concatenate, as for a
zonotope, and each half of the concatenated coefficient vector answers only to
its own constraints.

That last part is `comap` and `and` and nothing else — pull each polytope back
along the projection onto its block, then intersect. No matrix rows are
assembled and no sum has to be split, which is what carrying the constraints as
a polytope buys.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.plus (C₁ C₂ : ConZonotope α) : ConZonotope α where
  h := C₁.h + C₂.h
  c := C₁.c + C₂.c
  G := Fin.append C₁.G C₂.G
  P := (C₁.P.comap (blockLeft C₁.h C₂.h)).and (C₂.P.comap (blockRight C₁.h C₂.h))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
