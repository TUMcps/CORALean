module

public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorMargin
public import CORALean.ContSet.HPolytope.Float.Operations.IneqsContainBall
public import CORALean.ContSet.Zonotope.Float.Operations.BallCert

@[expose] public section

/-!
# `ConZonotope.interiorCert`

The check that a float constrained zonotope contains a whole box of points around
`y₀ = c + G β₀`, for a coefficient vector `β₀` and a right inverse `H` of the generator matrix the
caller proposes. With a margin `δ`: the unit box and every inequality row keep their slack
under a perturbation of `β₀` by at most `δ` in every coefficient (the rows by the constraint's
own `HPolytope.ineqsContainBall`, #174), and `Zonotope.ballCert` reaches
every vector within `B` with coefficients of size at most `δ`. Then every point whose distance to
`y₀` is at most `B` in every entry is in the nominal set (`ConZonotope.aux_box_subset`).

An equality row leaves no slack to perturb into, so a polytope with one fails the check, as
does every result whose rounded rows `ConZonotope.anchorSlab` kept as equalities; those it
wrote as inequality pairs (`HPolytope.slab`) keep their slack.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.interiorCert (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (H : Mat 𝕋 cZ.h n) (β₀ : Vec 𝕋 cZ.h)
    (δ B : 𝕋) : Bool :=
  le zero δ
    && (List.finRange cZ.h).all (fun j => le (addUp (absolute (β₀ j)) δ) one)
    && cZ.P.ineqsContainBall β₀ δ
    && (cZ.P.me == 0)
    && Zonotope.ballCert (fun i j => cZ.G j i) H B δ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
