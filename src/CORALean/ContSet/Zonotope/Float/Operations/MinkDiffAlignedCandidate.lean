import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.minkDiffAlignedCandidate`, over a floating-point scalar

The float candidate for `Real.Zonotope.minkDiffAligned`'s result, [1, Prop. 5]'s closed form
`(c₁ - c₂, G₁ - G₂)`, one named `let` per step. A difference is a guarantee, so every rounding
goes *inward*: each generator difference `g₁ᵢ - g₂ᵢ` is rounded towards zero, and then shrunk by
the factor `ρ ∈ (0, 1]` the caller picks, again towards zero. `ρ` is not in [1]: at aligned
generators the closed form is exact, so the containment check of `Zonotope.minkDiffAligned` has
no slack at all, and fails it even where every entry rounds exactly (`minkDiffAlignedOpt` in
`Examples/RunnableFloat.lean`). `ρ = 1` is CORA's own computation; `ρ < 1` is the slack.

Nothing here is trusted: rounding the centre may move the candidate off the real result, and
the operands need not be aligned at all. `Zonotope.minkDiffAligned` returns it only once
certified.

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

/-- `(c₁ - c₂, ρ · (G₁ - G₂))`, [1, Prop. 5] with the generators shrunk by `ρ`; rounded inward,
checked by `minkDiffAligned`. `hh` casts `Z₂`'s generators against `Z₁`'s own index. -/
def Zonotope.minkDiffAlignedCandidate (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (hh : Z₁.h = Z₂.h) (ρ : 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  let c := fun r => subDown (Z₁.c r) (Z₂.c r)  -- c₁ - c₂
  let diff := fun i r =>  -- g₁ᵢ - g₂ᵢ, rounded towards zero
    if le zero (subDown (Z₁.G i r) (Z₂.G (Fin.cast hh i) r)) then
      subDown (Z₁.G i r) (Z₂.G (Fin.cast hh i) r)
    else subUp (Z₁.G i r) (Z₂.G (Fin.cast hh i) r)
  let G := fun i r =>  -- ρ · (g₁ᵢ - g₂ᵢ), rounded towards zero
    if le zero (diff i r) then mulDown ρ (diff i r) else mulUp ρ (diff i r)
  { h := Z₁.h, c := c, G := G, E := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
