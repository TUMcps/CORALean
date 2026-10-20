module

public import CORALean.ContSet.PolyZonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapDep

@[expose] public section

/-!
# `PolyZonotope.quadMap`

The operation the representation exists for, rounded. The bookkeeping is the exact layer's and
none of it rounds; only the `(h+1)²` generators `Gᵢᵀ Q Gⱼ` are computed and charged. Each is
two rounded steps: `Q *ᵥ Gⱼ` comes back as an *interval*, and `quadDown`/`quadUp` take it as a
pair of bounds and pick per term with `minimum`/`maximum`. `quadMapDep` needs an empty
independent block and error box, which `absorbRounding` supplies, so it is done first.

## Inputs
* `Q` – family of quadratic form matrices
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope enclosing the quadratic image
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.quadMap (Q : Fin m → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 m) := PolyZonotope.quadMapDep Q pZ.absorbRounding

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
