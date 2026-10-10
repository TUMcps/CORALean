import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ENNReal.Basic

/-!
# `Zonotope.dominantScore`

The score `priv_volumeFilter` ranks a candidate basis `P` by: a rank-deficient `P` is `inf`;
otherwise the volume of `P · zonotope(interval(P⁺ Z))`, the parallelotope the basis encloses
`Z` in. With `P` square and invertible, `P⁺ = P⁻¹`, the box has radii `ρₖ = Σⱼ |(P⁻¹ gⱼ)ₖ|`,
and the parallelotope's generators are `P`'s columns scaled by `ρₖ`, so its volume is
`2ⁿ |det P| ∏ₖ ρₖ`.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `priv_volumeFilter`'s score of the basis `P` for `Z`: `⊤` if `P` is singular, else the volume
`2ⁿ |det P| ∏ₖ Σⱼ |(P⁻¹ gⱼ)ₖ|` of `P · box(P⁻¹ Z)`. -/
noncomputable def Zonotope.dominantScore (Z : Zonotope (Vec ℝ n)) (P : Mat ℝ n n) : ENNReal :=
  if P.det = 0 then ⊤                                                    -- rank(P) < d: inf
  else ENNReal.ofReal (2 ^ n * |P.det| * ∏ k, ∑ j, |(P⁻¹ *ᵥ Z.G j) k|)   -- volume(P*zonotope(I))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
