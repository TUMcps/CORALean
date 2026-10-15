module

public import CORALean.ContSet.Zonotope.Float.Operations.RightInvQ

@[expose] public section

/-!
# `Zonotope.rightInvGain`

The certificate that a candidate right inverse `H` (`n × q`) of a matrix `G` (`q × n`) solves
every system `G β = d` up to a known factor: with `κ = rightInvQ G H` bounding the absolute row
sums of `1 - G H`, it checks `1 - κ > 0` with outward rounding and returns
`γ ≥ maxⱼ ∑ₖ |Hⱼₖ| / (1 - κ)`, rounded up. Then every `d` with `|dᵢ| ≤ ε` is `G β` with every
`|βⱼ| ≤ γ ε` (`Zonotope.rightInvGain_solve`), the Neumann bound on a true right inverse. `none`
says only that this `H` was not good enough: a rank-deficient or ill-conditioned `G`, or a bad
candidate.

It serves wherever a rounded equality is kept as one: moving a point onto the stored hyperplanes
costs at most `γ` times the residual (`HPolytope.anchorEqs`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.rightInvGain (G : Mat 𝕋 q n) (H : Mat 𝕋 n q) : Option 𝕋 :=
  -- `1 - κ`, rounded down, where `κ` bounds the row sums of `|1 - G H|`
  let d := subDown one (Zonotope.rightInvQ G H)
  if ltStrict zero d then some (divUp (maximumOver (radius H)) d) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
