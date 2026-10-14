module

public import CORALean.ContSet.Zonotope.Float.Operations.MethCBasis
public import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
public import CORALean.ContSet.Zonotope.Float.Operations.MethCQ
public import CORALean.ContSet.Zonotope.Float.Operations.MethCReach
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Zonotope.reduceMethC`

CORA's `reduce(Z, 'methC', o)` [1] in its enclosing form: a parallelotope `c + P [-ρ, ρ]ⁿ` along a
basis `P` of `n` of the generators. Where the exact layer inverts `P` and boxes `P⁻¹ Z` per
coordinate, a float layer can only check an inverse: `H` is a candidate (`basisInverse`) and
`methCQ ≤ 1/2` says it is good enough, whereupon the coordinates of the generators in the basis are
at most `ρ = 2 methCReach` in magnitude, one bound for all of them. If the check fails, or there
is no room to reduce, the set is returned unchanged. The product `ρ P` is stored from below and
its gap paid into the box.

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025). No
      paper behind the rule was confirmed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.reduceMethC (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) : Zonotope (Vec 𝕋 n) :=
  if o * n < Z.h then
    -- a basis of generators, and a candidate inverse of it
    let P := Z.methCBasis
    let H := Zonotope.basisInverse P
    if le (Zonotope.methCQ H P) (half one) = true then
      let ρ := addUp (Zonotope.methCReach H fun i j => Z.G j i)
        (Zonotope.methCReach H fun i j => Z.G j i)
      { h := n
        c := Z.c
        G := fun k i => mulDown ρ (P i k)
        I_error := Z.I_error.plus (Zonotope.generatorError fun i k =>
          subUp (mulUp ρ (P i k)) (mulDown ρ (P i k))) }
    else Z
  else Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
