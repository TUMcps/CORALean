module

public import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# `ConZonotope.conIntersect` over a floating-point scalar

CORA's `@conZonotope/conIntersect` [1, Prop. 1] on the stored floats: the points of `cZ₁`
whose image under `M` lies in `cZ₂`. As over ℝ the coefficient vectors are stacked, each set
keeping its own constraints, the first set's centre and generators kept and the second block of
generators zero; the agreement rows `M G₁ β₁ - G₂ β₂ = c₂ - M c₁` are built from the float
image `Zonotope.mtimes M` of the first set's zonotope part (centre and generators rounded down,
the rest of `M (c₁ + G₁ β₁ + e₁)` in its error box), and, as in the float `intersection`, their
right-hand side is an interval holding `c₂ - M c₁` plus every difference of the two error boxes,
rounded outward. So the result is outer, not exact.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.conIntersect (cZ₁ : ConZonotope 𝕋 (Vec 𝕋 n)) (cZ₂ : ConZonotope 𝕋 (Vec 𝕋 m))
    (M : Mat 𝕋 m n) :
    ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- M (c₁ + G₁ β₁ + e₁): centre and generators rounded down, the rest in a box
  let W := Zonotope.mtimes M ⟨cZ₁.h, cZ₁.c, cZ₁.G, cZ₁.I_error⟩
  -- Z = [c₁, G₁, zeros(size(G₂))]
  let G : Fin (cZ₁.h + cZ₂.h) → Vec 𝕋 n := Fin.append cZ₁.G fun _ _ => zero
  -- A = blkdiag(A₁, A₂), b = [b₁; b₂]
  let P := (cZ₁.P.padLeft cZ₂.h).intersection (HPolytope.padRight cZ₁.h cZ₂.P)
  -- A = [A; M G₁, -G₂]
  let Aagree : Mat 𝕋 m (cZ₁.h + cZ₂.h) := fun i =>
    Fin.append (fun j => W.G j i) fun j => neg (cZ₂.G j i)
  -- b = [b; c₂ - M c₁], widened by what the two error boxes let the points differ by
  let bagree : Interval (Vec 𝕋 m) :=
    ⟨fun i => addDown (subDown (cZ₂.c i) (W.c i)) (subDown (cZ₂.I_error.inf i) (W.I_error.sup i)),
     fun i => addUp (subUp (cZ₂.c i) (W.c i)) (subUp (cZ₂.I_error.sup i) (W.I_error.inf i))⟩
  { h := cZ₁.h + cZ₂.h
    c := cZ₁.c
    G := G
    P := P.intersection (HPolytope.eqs Aagree bagree)
    I_error := cZ₁.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
