import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffAlignedCandidate
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `Zonotope.minkDiffAligned`, over a floating-point scalar

CORA's `'exact'` case of `@zonotope/minkDiff` for aligned generators, [1, Prop. 5], as a
*checked* result: the float counterpart of `Real.Zonotope.minkDiffAligned`. At the real layer the
closed form is the difference exactly (`Real.Zonotope.minkDiffAligned_exact`), but only at a
scaling in `[0, 1]` (`Real.Zonotope.minkDiffAligned_not_inner`), and CORA's alignment test is a
tolerance on floats. So the float result is not trusted on the strength of either: the candidate
(`minkDiffAlignedCandidate`) is returned only once `Zonotope.containsZonotope`, with a right
inverse `H` of the minuend's generators the caller proposes, certifies that the candidate plus the
subtrahend lies in the minuend, as `Zonotope.minkDiffRep` does. Unaligned operands, a scaling
outside `[0, 1]`, a wrong `ρ` or `H` give `none`, costing precision and never soundness.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 5]'s closed form, its generators shrunk by `ρ`, certified against the minuend with
the right inverse `H`; `none` where the check does not go through. -/
def Zonotope.minkDiffAligned (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (hh : Z₁.h = Z₂.h) (ρ : 𝕋)
    (H : Mat 𝕋 Z₁.h n) : Option (Zonotope (Vec 𝕋 n)) :=
  let D := Z₁.minkDiffAlignedCandidate Z₂ hh ρ
  if Z₁.containsZonotope (D.plus Z₂) H then some D else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
