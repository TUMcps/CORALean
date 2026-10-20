module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `HPolytope.rowScale`

The factor CORA's `priv_normalizeConstraints(..., 'A')` divides row `i` by, on the stored
floats: `1 / ‖Aᵢ‖₂`, the norm rounded up by `p` Newton steps (`normUp`) and the quotient rounded
up, or `1` when the norm is not certified positive (CORA leaves a zero row as it is). Only its
positivity is ever used: a row scaled by a positive number is the same halfspace.

## Inputs
* `p` – natural number
* `P` – H-polytope
* `i` – index below `P.m`

## Output
* `1 / ‖Aᵢ‖₂` with the norm and the quotient rounded up, or `1` for an uncertified norm
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.rowScale (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (i : Fin P.m) : 𝕋 :=
  let nrm := normUp p (P.A i)                                -- ‖Aᵢ‖₂, rounded up
  if ltStrict zero nrm then divUp one nrm else one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
