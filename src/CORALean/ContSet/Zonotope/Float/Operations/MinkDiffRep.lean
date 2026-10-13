import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffRepCandidate
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `Zonotope.minkDiffRep`, over a floating-point scalar

CORA's `@zonotope/minkDiff` as a *checked representation*, the float counterpart of
`Real.Zonotope.minkDiffRep`. A Minkowski difference is a guarantee, so unlike every other float
operation this one must return a **subset** of the real difference. The candidate
(`minkDiffRepCandidate`) is rounded inward, but rounding can still move it off the real result,
so it is returned only once `Zonotope.containsZonotope`, with a right inverse `H` of the
minuend's generators the caller proposes, certifies that the candidate plus the subtrahend lies in
the minuend. A wrong `M`, `ρ` or `H` gives `none`, costing precision and never soundness. `some`
proves the candidate lies in the difference; `none` refutes nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The difference at the representation `M`, margin shrunk by `ρ`, certified against the
minuend with the right inverse `H`; `none` where the check does not go through. -/
def Zonotope.minkDiffRep (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (M : Fin Z₁.h → Fin Z₂.h → 𝕋) (ρ : 𝕋)
    (H : Mat 𝕋 Z₁.h n) : Option (Zonotope (Vec 𝕋 n)) :=
  let D := Z₁.minkDiffRepCandidate Z₂ M ρ
  if Z₁.containsZonotope (D.plus Z₂) H then some D else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
