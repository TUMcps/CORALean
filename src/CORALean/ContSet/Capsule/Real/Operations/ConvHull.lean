module

public import CORALean.ContSet.Capsule.Real.Operations.Radius

@[expose] public section

/-!
# `Capsule.convHull`

CORA's `@capsule/convHull_.m` for two capsules: the centres' midpoint `c_`, the generator `g_`
from it to the first centre, and the larger of the two radii `‖g‖₂ + r`, a ball around that
segment. The hull of two capsules is not a capsule, so this encloses it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Capsule `convHull_` capsule, as in CORA: `c_ = (c + S.c)/2`, `g_ = c - c_`,
`r_ = max(‖g‖₂ + r, ‖S.g‖₂ + S.r)`. -/
noncomputable def Capsule.convHull (C S : Capsule n) : Capsule n :=
  let c_ := (1 / 2 : ℝ) • (C.c + S.c)
  let g_ := C.c - c_
  let r_ := max C.radius S.radius
  ⟨c_, g_, r_⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
