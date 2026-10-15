module

public import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesIntervalMatCost

@[expose] public section

/-!
# `ConZonotope.mtimesIntervalMatCost`

Asserted, not proved: `Operations/MtimesIntervalMat.lean` reads the radius off `cZ.zonotope`, a
conversion that repackages fields and writes its `n * (1 + h)` scalars, and pulls the polytope back
along `blockLeft`, a block embedding, writing its `(r + re) * (h + m + 1)` entries. The count is
`Zonotope.mtimesIntervalMatCost`'s plus those writes. The bound the constraints could tighten is
not computed, which is why this is no dearer than the unconstrained case.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.mtimesIntervalMat` costs at `IM : Interval (Mat ℝ m n)` and `h` generators,
a constraint polytope of `r` inequality and `re` equality rows: the zonotope's, the conversion's
writes and those of the polytope pulled back to `h + m` coefficients. -/
def ConZonotope.mtimesIntervalMatCost (m n h r re : ℕ) : Cost :=
  Zonotope.mtimesIntervalMatCost m n h + ⟨n * (1 + h) + (r + re) * (h + m + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
