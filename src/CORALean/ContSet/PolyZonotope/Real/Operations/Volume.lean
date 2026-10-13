module

public import CORALean.ContSet.PolyZonotope.Real.Operations.JacobianDetIntegral
public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent

@[expose] public section

/-!
# `PolyZonotope.volume`

CORA's `@polyZonotope/volume_`: the independent generators become dependent ones
(`dependent`), and then, with exactly as many factors as dimensions, the integral of the
Jacobian determinant over the factor cube `[-1,1]ᵖ`. With fewer factors than dimensions the
volume is `0`; with more CORA throws `CORA:notSupported`, which is `none`.

The integrand is the *signed* determinant. It is the volume of the image only where the
map is injective and the determinant does not change sign, and CORA's own comment claims
more (exactness where `det J ≠ 0`, an over-approximation otherwise); see
`volume_neg_example`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope/volume_`; `none` where CORA throws (more factors than dimensions). -/
noncomputable def PolyZonotope.volume (pZ : PolyZonotope (Vec ℝ n)) : Option ℝ :=
  -- redefine independent generators as new dependent generators
  let pZ' := if pZ.q = 0 then pZ else pZ.dependent
  if pZ'.p < n then some 0
  else if h : pZ'.p = n then some (pZ'.jacobianDetIntegral h)
  else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
