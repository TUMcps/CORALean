import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffStretch
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `Zonotope.minkDiffStretchInner`, over a floating-point scalar

CORA's `'inner'` method of `@zonotope/minkDiff`, [1, Thm. 4], as a *checked* result. At the real
layer the stretched minuend is inside the difference once `μ` meets [1, Thm. 4]'s halfspace
constraint (`Real.Zonotope.minkDiffStretch_inner`), a constraint CORA solves for by a linear
program in floating point. Neither is trusted here: the float `minkDiffStretch` at the caller's
`μ` is returned only once `Zonotope.containsZonotope`, with a right inverse `H` of the minuend's
generators, certifies that it plus the subtrahend lies in the minuend, as `Zonotope.minkDiffRep`
does. An infeasible `μ`, or one feasible with no slack left for rounding, or a wrong `H` gives
`none`, costing precision and never soundness.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 4]'s stretched minuend at `μ`, certified against the minuend with the right inverse
`H`; `none` where the check does not go through. -/
def Zonotope.minkDiffStretchInner (Z₁ Z₂ : Zonotope 𝕋 n) (μ : Fin Z₁.h → 𝕋)
    (H : Mat 𝕋 Z₁.h n) : Option (Zonotope 𝕋 n) :=
  let D := Z₁.minkDiffStretch Z₂ μ
  if Z₁.containsZonotope (D.plus Z₂) H then some D else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
