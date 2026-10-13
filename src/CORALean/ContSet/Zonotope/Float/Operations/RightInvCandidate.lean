import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse

/-!
# `Zonotope.rightInvCandidate`

A candidate right inverse of a generator matrix `G` (`n × h`): `Gᵀ (G Gᵀ)⁻¹`, the Gram matrix
formed with upward roundings and inverted by `Zonotope.basisInverse`. It is not trusted:
`Zonotope.ballCert` checks `G H` against the identity, so a rank-deficient `G`, a zero pivot or a
rounding that spoils the inverse costs the `true` and nothing else.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.rightInvCandidate (G : Mat 𝕋 n h) : Mat 𝕋 h n :=
  let gram : Mat 𝕋 n n := fun i j => dotUp (fun l => G i l) fun l => G j l
  let Ginv := Zonotope.basisInverse gram
  fun j i => dotUp (fun l => G l j) fun l => Ginv l i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
