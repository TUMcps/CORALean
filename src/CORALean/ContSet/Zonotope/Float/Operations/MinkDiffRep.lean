module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.minkDiffRep`, over a floating-point scalar

CORA's `@zonotope/minkDiff` as a *checked representation*, the float counterpart of
`Real.Zonotope.minkDiffRep`. A Minkowski difference is a guarantee, so unlike every other float
operation this one must return a **subset** of the real difference. The candidate
(`aux_minkDiffRepCandidate`) is rounded inward, but rounding can still move it off the real result,
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The candidate difference at the representation `M` (`M i j` writes `Z₂`'s `j`-th generator in
`Z₁`'s `i`-th), with the margin shrunk by `ρ`; rounded inward, checked by `minkDiffRep`. -/
def Zonotope.aux_minkDiffRepCandidate (Z₁ Z₂ : Zonotope (Vec 𝕋 n))
    (M : Fin Z₁.h → Fin Z₂.h → 𝕋) (ρ : 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  let c := fun r => subDown (Z₁.c r) (Z₂.c r)  -- c₁ - c₂
  let rowSum := fun i => sumUp fun j => maximum (M i j) (neg (M i j))  -- ∑ⱼ |Mᵢⱼ|, rounded up
  let margin := fun i => maximum zero (subDown one (rowSum i))  -- 1 - ∑ⱼ |Mᵢⱼ|, rounded down
  let scale := fun i => mulDown ρ (margin i)  -- shrunk by ρ
  let G := fun i r =>  -- scale i · gᵢ, rounded towards zero
    if le zero (Z₁.G i r) then mulDown (scale i) (Z₁.G i r) else mulUp (scale i) (Z₁.G i r)
  { h := Z₁.h, c := c, G := G, I_error := Interval.origin n }


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The difference at the representation `M`, margin shrunk by `ρ`, certified against the
minuend with the right inverse `H`; `none` where the check does not go through. -/
def Zonotope.minkDiffRep (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (M : Fin Z₁.h → Fin Z₂.h → 𝕋) (ρ : 𝕋)
    (H : Mat 𝕋 Z₁.h n) : Option (Zonotope (Vec 𝕋 n)) :=
  let D := Z₁.aux_minkDiffRepCandidate Z₂ M ρ
  if Z₁.containsZonotope (D.plus Z₂) H then some D else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
