module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.minkDiffAligned`, over a floating-point scalar

CORA's `'exact'` case of `@zonotope/minkDiff` for aligned generators, [1, Prop. 5], as a *checked*
result: the float counterpart of `Real.Zonotope.minkDiffAligned`. At the real layer the closed form
is the difference exactly (`Real.Zonotope.minkDiffAligned_exact`), but only at a scaling in `[0, 1]`
(`Real.Zonotope.minkDiffAligned_not_inner`), and CORA's alignment test is a tolerance on floats. So
the candidate (`aux_minkDiffAlignedCandidate`) is returned only once `Zonotope.containsZonotope`,
with a right inverse `H` of the minuend's generators the caller proposes, certifies that the
candidate plus the subtrahend lies in the minuend, as `Zonotope.minkDiffRep` does. Unaligned
operands or a wrong `ρ` or `H` give `none`, costing precision and never soundness.

## Inputs
* `Z₁` – minuend zonotope
* `Z₂` – subtrahend zonotope
* `ρ` – generator shrink factor
* `H` – candidate right inverse

## Hypotheses
* `hh` – equal generator counts

## Output
* shrunk difference zonotope, if the check passes

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(c₁ - c₂, ρ · (G₁ - G₂))`, [1, Prop. 5] with the generators shrunk by `ρ`; rounded inward,
checked by `minkDiffAligned`. `hh` casts `Z₂`'s generators against `Z₁`'s own index. -/
def Zonotope.aux_minkDiffAlignedCandidate (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (hh : Z₁.h = Z₂.h) (ρ : 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  let c := fun r => subDown (Z₁.c r) (Z₂.c r)  -- c₁ - c₂
  let diff := fun i r =>  -- g₁ᵢ - g₂ᵢ, rounded towards zero
    if le zero (subDown (Z₁.G i r) (Z₂.G (Fin.cast hh i) r)) then
      subDown (Z₁.G i r) (Z₂.G (Fin.cast hh i) r)
    else subUp (Z₁.G i r) (Z₂.G (Fin.cast hh i) r)
  let G := fun i r =>  -- ρ · (g₁ᵢ - g₂ᵢ), rounded towards zero
    if le zero (diff i r) then mulDown ρ (diff i r) else mulUp ρ (diff i r)
  { h := Z₁.h, c := c, G := G, I_error := Interval.origin n }


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 5]'s closed form, its generators shrunk by `ρ`, certified against the minuend with
the right inverse `H`; `none` where the check does not go through. -/
def Zonotope.minkDiffAligned (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (hh : Z₁.h = Z₂.h) (ρ : 𝕋)
    (H : Mat 𝕋 Z₁.h n) : Option (Zonotope (Vec 𝕋 n)) :=
  let D := Z₁.aux_minkDiffAlignedCandidate Z₂ hh ρ
  if Z₁.containsZonotope (D.plus Z₂) H then some D else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
