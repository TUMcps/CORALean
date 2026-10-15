module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConPolyZono.intersectionCost`

Asserted, not proved: `intersection` runs `intersectionDep` on the two
`dependent` sets — free — at zero tolerance. `intersectionDep` builds
`agreeRow`, which negates each of `cPZ₂`'s `h₂` dependent generators once per
output coordinate, `n * h₂` negations, and `intersectionB`, which is one
subtraction and one addition per coordinate for each of `inf` and `sup`,
`4 * n`. Everything else — `plusA`, `PolyZonotope.plusE`, `appendE` — lays a
field out block-diagonally and is free.

`h₂` is the *dependent* count `intersectionDep` sees, `cPZ₂.h + cPZ₂.qI` by
`dependent`, which `Complexity/Space/Theorems/IntersectionP.lean` states as the `h`
`intersectionDep`'s second operand carries.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.intersection` costs at `Vec ℝ n`, `cPZ₂` holding `h₂`
dependent generators after `dependent`: the two conversions free, the
agreement rows' negations and the bound's arithmetic. -/
def ConPolyZono.intersectionCost (n h₂ : ℕ) : Cost :=
  ConPolyZono.dependentCost + ConPolyZono.dependentCost + (⟨n * h₂⟩ + ⟨4 * n⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
