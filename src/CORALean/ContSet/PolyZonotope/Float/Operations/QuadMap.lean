import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# `PolyZonotope.quadMap`

The operation the representation exists for, rounded. The bookkeeping is the
exact layer's and none of it rounds: `extE` widens the exponent matrix by the
centre's zero column, `quadMapE` adds two columns over ℕ, and pairs are indexed
through `finProdFinEquiv`. Only the `(h+1)²` generators `Gᵢᵀ Q Gⱼ` are computed,
and only they are charged.

Each is a bilinear form and so two rounded steps, which is where a directed
rounding stops composing: `Q *ᵥ Gⱼ` comes back as an *interval*, and multiplying
an interval by `Gᵢ` cannot round in one direction without knowing the sign of
`Gᵢ`. `quadDown`/`quadUp` therefore take the middle vector as a pair of bounds
and pick per term with `minimum`/`maximum`, which is `Interval.mtimes`'s shape
for exactly this reason.

`quadMapDep` needs an empty independent block *and* an empty error box — a
quadratic map is not additive, so a box cannot be carried through it beside the
nominal part. `dependent` supplies both, which is why it is the first thing
`quadMap` does.

The error box holds `(h+1)²` terms per coordinate where `mtimes` holds `h`. That
is where a polynomial zonotope's rounding actually accumulates, and it is a
reason to `compact` before mapping rather than after.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- The centre as generator zero, so a point is one sum. -/
def PolyZonotope.extG (S : PolyZonotope 𝕋 n) : Mat 𝕋 n (S.h + 1) :=
  fun i => Fin.cons (S.c i) (S.G i)

/-- The exponent matrix widened to match, the centre's column being zero — its
monomial is `1`, which is what the centre needs to be. -/
def PolyZonotope.extE (S : PolyZonotope 𝕋 n) : Fin S.p → Fin (S.h + 1) → ℕ :=
  fun k => Fin.cons 0 (S.E k)

/-- The image's exponent column, the two columns added. Over ℕ, so exact. -/
def PolyZonotope.quadMapE (S : PolyZonotope 𝕋 n) :
    Fin S.p → Fin ((S.h + 1) * (S.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S k (finProdFinEquiv.symm l).2

/-- `g ⬝ᵥ w` rounded down, where `w` is known only to lie in `[wlo, whi]`. -/
def PolyZonotope.quadDown (g wlo whi : Vec 𝕋 n) : 𝕋 :=
  sumDown fun r => minimum (mulDown (g r) (wlo r)) (mulDown (g r) (whi r))

def PolyZonotope.quadUp (g wlo whi : Vec 𝕋 n) : 𝕋 :=
  sumUp fun r => maximum (mulUp (g r) (wlo r)) (mulUp (g r) (whi r))

/-- Generator `(i, j)` of the image, `Gᵢᵀ Q Gⱼ`, rounded down: `Q *ᵥ Gⱼ` in both
directions first, then the outer product against `Gᵢ` over that interval. -/
def PolyZonotope.quadMapGDown (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    Mat 𝕋 m ((S.h + 1) * (S.h + 1)) :=
  fun k l => PolyZonotope.quadDown (fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).1)
    (mulVecDown (Q k) fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).2)
    (mulVecUp (Q k) fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).2)

def PolyZonotope.quadMapGUp (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    Mat 𝕋 m ((S.h + 1) * (S.h + 1)) :=
  fun k l => PolyZonotope.quadUp (fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).1)
    (mulVecDown (Q k) fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).2)
    (mulVecUp (Q k) fun r => PolyZonotope.extG S r (finProdFinEquiv.symm l).2)

/-- How far a stored generator can be from the exact bilinear form. -/
def PolyZonotope.quadMapGDiff (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    Mat 𝕋 m ((S.h + 1) * (S.h + 1)) :=
  fun k l => subUp (PolyZonotope.quadMapGUp Q S k l) (PolyZonotope.quadMapGDown Q S k l)

/-- The map on a set with no independent block and no error box. Sound only
there, so nothing calls it directly. -/
def PolyZonotope.quadMapDep (Q : Fin m → Mat 𝕋 n n) (S : PolyZonotope 𝕋 n) :
    PolyZonotope 𝕋 m where
  p := S.p
  h := (S.h + 1) * (S.h + 1)
  q := 0
  c := fun _ => zero
  G := PolyZonotope.quadMapGDown Q S
  E := PolyZonotope.quadMapE S
  GI := fun _ => Fin.elim0
  err := PolyZonotope.generatorError (PolyZonotope.quadMapGDiff Q S)

def PolyZonotope.quadMap (Q : Fin m → Mat 𝕋 n n) (PZ : PolyZonotope 𝕋 n) :
    PolyZonotope 𝕋 m := PolyZonotope.quadMapDep Q PZ.dependent

end CORALean.Float
