module

public import CORALean.ContSet.ConZonotope.Float.Operations.AnchorSlab
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight

@[expose] public section

/-!
# `ConZonotope.intersection`

CORA's `@conZonotope/and_` [1, Prop. 1] over a floating-point scalar. Both coefficient vectors are
concatenated, each half keeps its own constraints, and one row per coordinate demands that the two
points agree, `G₁ β₁ - G₂ β₂ = c₂ - c₁`; only the first generator block is then kept. Nothing rounds
but the agreement rows' right-hand side, which has to hold every value the two nominal points can
differ by once each sits in its error box: an interval, its ends rounded outward. The rows stay
equalities at its upper end where `ConZonotope.anchorSlab` certifies them, else they become the slab
between the two ends. The result keeps the first operand's box, so widened. CORA's closing
`compact_(…,'zeros')` changes no point and is not done here, as at the exact layer.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Output
* the intersection of the two sets

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
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
  let P := (cZ₁.P.padLeft cZ₂.h).stackRows (HPolytope.padRight cZ₁.h cZ₂.P)
  -- A = [A; G₁, -G₂]
  let Aagree : Mat 𝕋 n (cZ₁.h + cZ₂.h) := fun i =>
    Fin.append (fun j => cZ₁.G j i) fun j => neg (cZ₂.G j i)
  -- b = [b; c₂ - c₁], widened by what the two error boxes let the points differ by
  let bagree : Interval (Vec 𝕋 n) :=
    ⟨fun i => addDown (subDown (cZ₂.c i) (cZ₁.c i))
        (subDown (cZ₂.I_error.inf i) (cZ₁.I_error.sup i)),
     fun i => addUp (subUp (cZ₂.c i) (cZ₁.c i)) (subUp (cZ₂.I_error.sup i) (cZ₁.I_error.inf i))⟩
  -- the agreement rows kept as equalities where certified (`anchorSlab`), else as a slab
  ConZonotope.anchorSlab { h := cZ₁.h + cZ₂.h, c := cZ₁.c, G := G, P := P, I_error := cZ₁.I_error }
    Aagree bagree.inf bagree.sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
