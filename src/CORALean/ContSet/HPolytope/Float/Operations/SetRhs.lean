module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.setRhs`: new right-hand sides, their rounding in the slacks

An operation that computes a row's new right-hand side in floats knows it only between two
roundings, `lo ≤ r ≤ hi`. This stores the lower end as the row's bound and pays the width
`hi - lo`, rounded up, into the row's slack beside what the slack held (#218): an inequality then
reads `Aᵢ x ≤ loᵢ + |b_errorᵢ| + (hiᵢ - loᵢ)`, at least `rᵢ + |b_errorᵢ|`, and an equality the slab
`|Aeᵢ x - loEᵢ| ≤ |be_errorᵢ| + (hiEᵢ - loEᵢ)`, which holds wherever `|Aeᵢ x - rEᵢ| ≤ |be_errorᵢ|`
does. So no bound is raised, an equality stays an equality, and the rows and the error box are
kept; `HPolytope.mem_setRhs_nominal` is the guarantee. The enclosures may depend on the point
read, which is how `scaleRows` pays the rounding of its scaled rows.

## Inputs
* `P` – H-polytope
* `lo` – vector of length `P.m`
* `hi` – vector of length `P.m`
* `loE` – vector of length `P.me`
* `hiE` – vector of length `P.me`

## Output
* `P` with right-hand sides `lo`, `loE` and each slack grown by the width to `hi`, `hiE`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` with the right-hand sides `lo` and `loE`, each row's slack grown by its width to `hi` or
`hiE`, rounded up. -/
def HPolytope.setRhs (P : HPolytope 𝕋 (Vec 𝕋 n)) (lo hi : Vec 𝕋 P.m) (loE hiE : Vec 𝕋 P.me) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  { P with
    b := lo
    be := loE
    b_error := fun i => addUp (absolute (P.b_error i)) (subUp (hi i) (lo i))
    be_error := fun i => addUp (absolute (P.be_error i)) (subUp (hiE i) (loE i)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
