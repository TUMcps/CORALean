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

def ConZonotope.plus (cZ₁ cZ₂ : ConZonotope α) : ConZonotope α where
  h := cZ₁.h + cZ₂.h
  c := cZ₁.c + cZ₂.c
  G := Fin.append cZ₁.G cZ₂.G
  P := (cZ₁.P.comap (blockLeft cZ₁.h cZ₂.h)).and (cZ₂.P.comap (blockRight cZ₁.h cZ₂.h))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
