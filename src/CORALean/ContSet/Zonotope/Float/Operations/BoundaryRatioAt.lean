module

public import CORALean.ContSet.Zonotope.Float.Operations.FacetNormal

@[expose] public section

/-!
# `Zonotope.boundaryRatioAt`, over a floating-point scalar

One facet's bound on the exit step of `boundaryPoint`. CORA solves a linear program for the largest
`t` with `startPoint + t * dir` in the zonotope; the zonotope is the intersection of the slabs `C x
<= C c + sum_u |C G_u|` of its facet normals `C` [1, Thm. 2], so `t` is at most `(C c + sum_u |C
G_u| - C startPoint) / (C dir)` at every `C` with `C dir > 0`, and the least of them is the exit
step. Here the quotient is rounded up: the numerator by `dotUp`, `sumUp` and `subUp` (the magnitude
of a dot product is at most the larger of the upper end and the negated lower end), the start
point's product from below, the denominator from below, with `none` where `ltStrict` cannot prove it
positive. The vector `C` is `facetNormal`'s rounded candidate; the bound holds at any vector, so a
rounded normal costs tightness and not soundness.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exit step the facet row at generator selection `S` allows, rounded up. -/
def Zonotope.boundaryRatioAt (Z : Zonotope (Vec 𝕋 (n + 1))) (dir start : Vec 𝕋 (n + 1))
    (S : Fin n → Fin Z.h) : Option 𝕋 :=
  let C := Z.facetNormal S                                                  -- facet normal
  let Δd := sumUp fun υ =>                                                  -- Σᵤ |C G⁽ᵘ⁾|
    maximum (dotUp C (Z.G υ)) (neg (dotDown C (Z.G υ)))
  let ρ := addUp (dotUp C Z.c) Δd                                           -- C c + Σᵤ |C G⁽ᵘ⁾|
  let num := subUp ρ (dotDown C start)                                      -- ρ - C startPoint
  let den := dotDown C dir                                                  -- C dir, from below
  if ltStrict zero den = true then some (divUp num den) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
