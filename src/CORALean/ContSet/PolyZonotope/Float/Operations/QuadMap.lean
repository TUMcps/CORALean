import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapDep

/-!
# `PolyZonotope.quadMap`

The operation the representation exists for, rounded. The bookkeeping is the
exact layer's and none of it rounds: `extE`, `quadMapE` and `finProdFinEquiv`
are all over ℕ. Only the `(h+1)²` generators `Gᵢᵀ Q Gⱼ` are computed and only
they are charged.

Each is a bilinear form and so two rounded steps, which is where a directed
rounding stops composing: `Q *ᵥ Gⱼ` comes back as an *interval*, and multiplying
an interval by `Gᵢ` cannot round in one direction without knowing the sign of
`Gᵢ`. `quadDown`/`quadUp` therefore take the middle vector as a pair of bounds
and pick per term with `minimum`/`maximum`, which is `Interval.mtimes`'s shape.

`quadMapDep` needs an empty independent block *and* an empty error box — a
quadratic map is not additive — which `dependent` supplies, and which is why it
is the first thing `quadMap` does. The error box then holds `(h+1)²` terms per
coordinate where `mtimes` holds `h`, which is a reason to `compact` before
mapping rather than after.
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
    PolyZonotope (Vec 𝕋 m) := PolyZonotope.quadMapDep Q pZ.dependent

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
