module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight

@[expose] public section

/-!
# `ConZonotope.intersection`

CORA's `@conZonotope/and_` [1, Prop. 1] over a floating-point scalar. Both
coefficient vectors are concatenated, each half keeps its own constraints, and
one row per coordinate demands that the two points agree,
`G₁ β₁ - G₂ β₂ = c₂ - c₁`; only the first generator block is then kept.

Nothing rounds but the agreement rows' right-hand side. The generators are
copied, `neg` is exact, and padding copies. What the right-hand side has to
hold is not `c₂ - c₁` but every value the two *nominal* points can differ by
once each sits in its own error box, `c₂ - c₁ + e₂ - e₁`: that is an interval,
which is exactly what a float equality row carries, and its two ends are
rounded outward. The result keeps the first operand's box, the point it
describes being the first operand's.

CORA's closing `compact_(…,'zeros')` drops zero rows and columns and changes no
point; it is not done here, as at the exact layer.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.intersection (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- Z = [c₁, G₁, zeros(size(G₂))]
  let G : Fin (cZ₁.h + cZ₂.h) → Vec 𝕋 n := Fin.append cZ₁.G fun _ _ => zero
  -- A = blkdiag(A₁, A₂), b = [b₁; b₂]
  let P := (cZ₁.P.padLeft cZ₂.h).intersection (HPolytope.padRight cZ₁.h cZ₂.P)
  -- A = [A; G₁, -G₂]
  let Aagree : Mat 𝕋 n (cZ₁.h + cZ₂.h) := fun i =>
    Fin.append (fun j => cZ₁.G j i) fun j => neg (cZ₂.G j i)
  -- b = [b; c₂ - c₁], widened by what the two error boxes let the points differ by
  let bagree : Interval (Vec 𝕋 n) :=
    ⟨fun i => addDown (subDown (cZ₂.c i) (cZ₁.c i))
        (subDown (cZ₂.I_error.inf i) (cZ₁.I_error.sup i)),
     fun i => addUp (subUp (cZ₂.c i) (cZ₁.c i)) (subUp (cZ₂.I_error.sup i) (cZ₁.I_error.inf i))⟩
  { h := cZ₁.h + cZ₂.h
    c := cZ₁.c
    G := G
    P := P.intersection (HPolytope.eqs Aagree bagree)
    I_error := cZ₁.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
