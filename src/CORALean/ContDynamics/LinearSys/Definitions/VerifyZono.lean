module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# A zonotope with a list of generators and a box, for the zonotope verification

The sets `LinearSys.verifyZonotopePassFloat` returns: a center `c`, generators `G` in a list (their
number changes from step to step as the input's generators are added and reduced) and the radius
`r` of a box about the center, `{c + Σⱼ βⱼ gⱼ + e | |βⱼ| ≤ 1, |eᵢ| ≤ rᵢ}`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A zonotope `⟨c, G⟩` plus the box of radius `r`, in `q` dimensions. -/
structure LinearSys.VerifyZono (𝕋 : Type) (q : ℕ) where
  /-- The center. -/
  c : Vec 𝕋 q
  /-- The generators, in order. -/
  G : List (Vec 𝕋 q)
  /-- The radius of the box about the center. -/
  r : Vec 𝕋 q

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
