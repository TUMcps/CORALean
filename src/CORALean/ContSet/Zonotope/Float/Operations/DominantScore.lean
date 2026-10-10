import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
import CORALean.ContSet.Zonotope.Float.Operations.DetCandidate

/-!
# `Zonotope.dominantScore`, over a floating-point scalar

The score `priv_volumeFilter` ranks a candidate basis `P` by: `inf` for a rank-deficient `P`, here
`none`; otherwise the volume of `P box(P⁻¹ Z)`, which for an invertible `P` is
`2ⁿ |det P| ∏ₖ Σⱼ |(P⁻¹ gⱼ)ₖ|`. The common factor `2ⁿ` does not change a ranking and is dropped.
`P⁻¹` is `Zonotope.basisInverse`, the determinant `Zonotope.detCandidate`, and `P` counts as
invertible when `ltStrict` proves the determinant candidate nonzero. A heuristic: the
enclosure `dominantDirections` returns is not read off this number.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `none` if `P` is not provably nonsingular, else `|det P| ∏ₖ Σⱼ |(P⁻¹ gⱼ)ₖ|`, rounded up. -/
def Zonotope.dominantScore (Z : Zonotope 𝕋 n) (P : Mat 𝕋 n n) : Option 𝕋 :=
  let d := absolute (Zonotope.detCandidate P)                             -- |det P|
  let Pinv := Zonotope.basisInverse P                                     -- P \ ·
  let ρ := fun k => sumUp fun j => absolute (dotUp (Pinv k) (Z.G j))     -- Σⱼ |(P⁻¹ gⱼ)ₖ|
  if ltStrict zero d = true then
    some ((List.finRange n).foldl (fun acc k => mulUp acc (ρ k)) d)       -- volume(P*zonotope(I))
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
