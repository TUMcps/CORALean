module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

@[expose] public section

/-!
# `PolyZonotope.padBack`

The set read over `r` further factors, appended after its own. Only the factor
count and the exponent matrix move; the center, both generator blocks and the
counts of them stay, so `padBack` changes no point and denotes the same set.

It exists for the product of two sets over *independent* factors, which `bilin`
cannot take as it stands: pad the left set at the back by the right set's
factors and the right set at the front by the left set's, and the two share one
factor set of `p₁ + p₂` in which each still ignores the other's half.

## Inputs
* `r` – number of added factors
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with r unused factors appended
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `r` fresh factors appended after the set's own, at exponent zero. -/
def PolyZonotope.padBack (r : ℕ) (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p + r
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := PolyZonotope.padE pZ.E r
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
