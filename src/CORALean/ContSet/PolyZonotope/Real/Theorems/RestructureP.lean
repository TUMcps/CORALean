module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure

@[expose] public section

/-!
# `restructure` adds one factor per coordinate

The price of `restructure_q`, and the reason the boxing is worth doing rather
than freeing each independent generator directly: `dependent` alone would add
`pZ.q` factors, however many that is, while boxing first fixes the count at the
dimension. CORA's `order` argument buys the same bound on the *dependent
generator* count, by pairing a stronger reduction with the same conversion.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the factor count grows by the dimension
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem PolyZonotope.restructure_p (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.restructure.p = pZ.p + n := by
  show pZ.p + (0 + n) = pZ.p + n
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
