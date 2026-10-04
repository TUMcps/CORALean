import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope
import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
import CORALean.ContSet.HPolytope.Real.Operations.IsLPCentre

/-!
# `ZonoBundle.IsCentre`

CORA's `@zonoBundle/center`: `cZ = conZonotope(zB)`, then `center(cZ)`, with `[]` for an empty
set. The centre of a constrained zonotope is a linear-program optimum (`ConZonotope.IsCentre`), so
it is the specification here too, on `conZonotopeAll`, the exact `conZonotope(zB)`.

Only the program of `polytope/center` over the coefficient domain `cZ.domain` is named: the
bundle's constrained zonotope carries its constraints as a polytope `P`, not in the form
`A β = b` that the null-space program of the full-dimensional branch of `conZonotope/center` is
stated for, so that branch is not modelled. `0 < k`: CORA answers `[]` for no members.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` is `c + G β` for a Chebyshev centre `β` of the coefficient domain of `conZonotope(zB)`. -/
def ZonoBundle.IsCentre (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) (x : Vec ℝ n) : Prop :=
  let cZ := zB.conZonotopeAll hk
  ∃ β : Vec ℝ cZ.h, cZ.domain.IsLPCentre β ∧ x = cZ.c + ∑ j, β j • cZ.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
