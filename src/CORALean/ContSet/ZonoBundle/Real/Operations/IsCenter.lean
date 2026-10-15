module

public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter

@[expose] public section

/-!
# `ZonoBundle.IsCenter`

CORA's `@zonoBundle/center`: `cZ = conZonotope(zB)`, then `center(cZ)`, with `[]` for an empty
set. The center of a constrained zonotope is a linear-program optimum (`ConZonotope.IsCenter`), so
it is the specification here too, on `conZonotopeAll`, the exact `conZonotope(zB)`.

Only the program of `polytope/center` over the coefficient domain `cZ.domain` is named: the
bundle's constrained zonotope carries its constraints as a polytope `P`, not in the form
`A β = b` that the null-space program of the full-dimensional branch of `conZonotope/center` is
stated for, so that branch is not modelled. `0 < k`: CORA answers `[]` for no members.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` is `c + G β` for a Chebyshev center `β` of the coefficient domain of `conZonotope(zB)`. -/
def ZonoBundle.IsCenter (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) (x : Vec ℝ n) : Prop :=
  let cZ := zB.conZonotopeAll hk
  ∃ β : Vec ℝ cZ.h, cZ.domain.IsLPCenter β ∧ x = cZ.c + ∑ j, β j • cZ.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
