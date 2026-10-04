import CORALean.ContSet.ConZonotope.Float.Operations.InteriorMargin
import CORALean.ContSet.Zonotope.Float.Operations.BallCert

/-!
# `ConZonotope.interiorCert`

The check that a float constrained zonotope contains a whole box of points around
`y₀ = c + G β₀`, for a coefficient vector `β₀` and a right inverse `H` of the generator matrix the
caller proposes. With a margin `δ`: the unit box, every inequality row and both ends of every
equality row's interval keep their slack under a perturbation of `β₀` by at most `δ` in every
coefficient (each row's absolute sum times `δ`, rounded upward), and `Zonotope.ballCert` reaches
every vector within `B` with coefficients of size at most `δ`. Then every point whose distance to
`y₀` is at most `B` in every entry is in the nominal set (`ConZonotope.aux_box_subset`).

The equalities of the real layer are the slab rows `be.inf ≤ Ae β ≤ be.sup` here, which is what
makes a strict margin possible; a `be` with `inf = sup` leaves none and the check fails.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.interiorCert (cZ : ConZonotope 𝕋 n) (H : Mat 𝕋 cZ.h n) (β₀ : Vec 𝕋 cZ.h)
    (δ B : 𝕋) : Bool :=
  le zero δ
    && (List.finRange cZ.h).all (fun j => le (addUp (absolute (β₀ j)) δ) one)
    && (List.finRange cZ.P.m).all (fun i =>
      le (addUp (dotUp (cZ.P.A i) β₀) (mulUp δ (radius cZ.P.A i))) (cZ.P.b i))
    && (List.finRange cZ.P.me).all (fun i =>
      le (addUp (dotUp (cZ.P.Ae i) β₀) (mulUp δ (radius cZ.P.Ae i))) (cZ.P.be.sup i)
        && le (cZ.P.be.inf i) (subDown (dotDown (cZ.P.Ae i) β₀) (mulUp δ (radius cZ.P.Ae i))))
    && Zonotope.ballCert cZ.G H B δ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
