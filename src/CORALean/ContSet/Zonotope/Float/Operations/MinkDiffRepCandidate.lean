import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.minkDiffRepCandidate`, over a floating-point scalar

The float candidate for `Real.Zonotope.minkDiffRep`'s result, one named `let` per step: the centre
`c₁ - c₂`, the row sums `∑ⱼ |Mᵢⱼ|` of the representation, the margin `1 - ∑ⱼ |Mᵢⱼ|`, and the
generators `margin · gᵢ`. A difference is a guarantee, so every rounding here goes *inward*: the
row sums are rounded up, so the margin down, and a scaled generator is rounded towards zero. The
margin is also shrunk by the factor `ρ ∈ (0, 1]` the caller picks, which leaves the slack the
containment check of `Zonotope.minkDiffRep` needs. Rounding may still move the candidate off the
real result, so it is not trusted: `Zonotope.minkDiffRep` returns it only once certified.

Orientation, pinned by `minkDiffNS*` in `Examples/RunnableFloat.lean`: generators are stored
generator-first (in `!![...]` each row is one), and `M i j` is the coefficient of `Z₁`'s generator
`i` in `Z₂`'s generator `j`. The example is non-square (`h₁ = 3`, `h₂ = 2`,
`M = [[½,0],[0,¼],[0,¼]]` for `Z₂`'s generators `(½,0)`, `(¼,½)` over `Z₁`'s `(1,0)`, `(0,1)`,
`(1,1)`), so summing over the wrong axis changes the generator count and margins, and `ρ = ½`
gives the hull `[-⅝,⅝] × [-¾,¾]`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The candidate difference at the representation `M` (`M i j` writes `Z₂`'s `j`-th generator in
`Z₁`'s `i`-th), with the margin shrunk by `ρ`; rounded inward, checked by `minkDiffRep`. -/
def Zonotope.minkDiffRepCandidate (Z₁ Z₂ : Zonotope (Vec 𝕋 n))
    (M : Fin Z₁.h → Fin Z₂.h → 𝕋) (ρ : 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  let c := fun r => subDown (Z₁.c r) (Z₂.c r)  -- c₁ - c₂
  let rowSum := fun i => sumUp fun j => maximum (M i j) (neg (M i j))  -- ∑ⱼ |Mᵢⱼ|, rounded up
  let margin := fun i => maximum zero (subDown one (rowSum i))  -- 1 - ∑ⱼ |Mᵢⱼ|, rounded down
  let scale := fun i => mulDown ρ (margin i)  -- shrunk by ρ
  let G := fun i r =>  -- scale i · gᵢ, rounded towards zero
    if le zero (Z₁.G i r) then mulDown (scale i) (Z₁.G i r) else mulUp (scale i) (Z₁.G i r)
  { h := Z₁.h, c := c, G := G, E := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
