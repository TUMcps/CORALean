import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

/-!
# `PolyZonotope.padBack`

The set read over `r` further factors, appended after its own. Only the factor
count and the exponent matrix move; the centre, both generator blocks and the
counts of them stay, so `padBack` changes no point and denotes the same set.

It exists for the product of two sets over *independent* factors, which `bilin`
cannot take as it stands: pad the left set at the back by the right set's
factors and the right set at the front by the left set's, and the two share one
factor set of `p₁ + p₂` in which each still ignores the other's half.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `r` fresh factors appended after the set's own, at exponent zero. -/
def PolyZonotope.padBack (r : ℕ) (S : PolyZonotope α) : PolyZonotope α where
  p := S.p + r
  h := S.h
  q := S.q
  c := S.c
  G := S.G
  E := PolyZonotope.padE S.E r
  GI := S.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
