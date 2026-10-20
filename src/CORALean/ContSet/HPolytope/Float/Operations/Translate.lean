module

public import CORALean.ContSet.HPolytope.Float.Operations.SetRhs

@[expose] public section

/-!
# `HPolytope.translate`, over a floating-point scalar

The first operation at this layer that actually rounds.

Shifting moves each bound by what its own row reads off the shift, which is a dot product
and so inexact: the shifted bound is known between its two roundings. `setRhs` stores the lower
one and pays the gap into the row's slack (#218), so an inequality's `b` is the shifted bound
rounded down and an equality stays an equality, a slab as wide as its slack and the gap; the
error box moves with the polytope unchanged.

## Inputs
* `t` – vector of length `n`
* `P` – H-polytope

## Output
* `P` shifted by `t`, each bound moved by its row's dot product with `t`, rounding in the slacks
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.translate (t : Vec 𝕋 n) (P : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- every bound moved by what its row reads off `t`, between its two roundings
  P.setRhs (fun i => addDown (P.b i) (dotDown (P.A i) t)) (fun i => addUp (P.b i) (dotUp (P.A i) t))
    (fun i => addDown (P.be i) (dotDown (P.Ae i) t)) (fun i => addUp (P.be i) (dotUp (P.Ae i) t))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
