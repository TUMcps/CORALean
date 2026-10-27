module

public import CORALean.ContSet.Zonotope.Float.Operations.MethCBasis
public import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.reduceMethC`

CORA's `reduce(Z, 'methC', o)` [1] in its enclosing form: a parallelotope `c + P [-ρ, ρ]ⁿ` along a
basis `P` of `n` of the generators. Where the exact layer inverts `P` and boxes `P⁻¹ Z` per
coordinate, a float layer can only check an inverse: `H` is a candidate (`basisInverse`) and
`step_methCQ ≤ 1/2` says it is good enough, whereupon the coordinates of the generators in the basis
are at most `ρ = 2 step_methCReach` in magnitude, one bound for all of them. If the check fails, or
there is no room to reduce, the set is returned unchanged. The product `ρ P` is stored from below
and its gap paid into the box.

## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* parallelotope enclosing the zonotope along a generator basis

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


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- An upper bound on `|1 - H P|`, entrywise. -/
@[step_of Zonotope.reduceMethC]
def Zonotope.step_methCResidual (H P : Mat 𝕋 n n) : Fin n → Fin n → 𝕋 := fun i j =>
  maximum
    (absolute (subDown (if i = j then one else zero) (dotUp (H i) fun l => P l j)))
    (absolute (subUp (if i = j then one else zero) (dotDown (H i) fun l => P l j)))

/-- An upper bound on `‖H G β‖∞` over the coefficient box. -/
@[step_of Zonotope.reduceMethC]
def Zonotope.step_methCReach (H : Mat 𝕋 n n) (G : Mat 𝕋 n h) : 𝕋 :=
  maximumOver fun i => sumUp fun j =>
    maximum (absolute (dotDown (H i) fun l => G l j)) (absolute (dotUp (H i) fun l => G l j))

/-- An upper bound on the largest absolute row sum of `1 - H P`. -/
@[step_of Zonotope.reduceMethC]
def Zonotope.step_methCQ (H P : Mat 𝕋 n n) : 𝕋 :=
  maximumOver fun i => sumUp fun j => Zonotope.step_methCResidual H P i j


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.reduceMethC (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) : Zonotope (Vec 𝕋 n) :=
  if o * n < Z.h then
    -- a basis of generators, and a candidate inverse of it
    let P := Z.methCBasis
    let H := Zonotope.basisInverse P
    if le (Zonotope.step_methCQ H P) (half one) = true then
      let ρ := addUp (Zonotope.step_methCReach H fun i j => Z.G j i)
        (Zonotope.step_methCReach H fun i j => Z.G j i)
      { h := n
        c := Z.c
        G := fun k i => mulDown ρ (P i k)
        I_error := Z.I_error.plus (Zonotope.generatorError fun i k =>
          subUp (mulUp ρ (P i k)) (mulDown ρ (P i k))) }
    else Z
  else Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
