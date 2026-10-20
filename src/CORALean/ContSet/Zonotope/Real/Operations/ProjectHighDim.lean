module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.Map

@[expose] public section

/-!
# `Zonotope.projectHighDim_`

CORA's `@zonotope/projectHighDim_`: the center and every generator written into the
coordinates `proj` of a zero vector of length `N`. `embed proj` is the zero-padding map, the
selection matrix transposed; it is linear, so this is `map` at it. CORA's assignment
`cnew(proj,:) = Z.c` overwrites on a repeated index, which `embed` sums instead, so the
statement of `projectHighDim__exact` assumes `proj` injective, as CORA's callers do.

## Inputs
* `Z` – zonotope
* `proj` – coordinate embedding

## Output
* zonotope embedded in the higher dimension
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.projectHighDim_ (Z : Zonotope (Vec ℝ n)) (proj : Fin n → Fin N) :
    Zonotope (Vec ℝ N) :=
  Z.map (Zonotope.embed proj)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
