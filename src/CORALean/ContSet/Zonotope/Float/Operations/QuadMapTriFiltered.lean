module

public import CORALean.ContSet.Zonotope.Float.Operations.CompactZeros
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri

@[expose] public section

/-!
# `Zonotope.quadMapTriFiltered`, over a floating-point scalar

CORA's `@zonotope/quadMap` of one zonotope as CORA returns it: `quadMapTri`, then, where two or
more of the `Q⁽ⁱ⁾` are nonzero, CORA's `nonzeroFilter` (`compactZeros`); where at most one is,
the box of the generators, one generator of the absolute row sums (`sumUp`). The box is taken only
where at most one coordinate of the generators is not certified zero, so that it is the segment
along that coordinate; otherwise `compactZeros` keeps the set. At most one nonzero `Q⁽ⁱ⁾` leaves
the other rows zero at `nearest`, where this is CORA's choice. Both branches hold the set of
`quadMapTri` (`quadMapTriFiltered_outer`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Output
* zonotope enclosing the quadratic image, with CORA's generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Whether `Q` has an entry that is not certified zero (CORA's `any(Q{i}(:))`). -/
@[step_of Zonotope.quadMapTriFiltered]
def Zonotope.step_quadMapTriFilteredUsed (Q : Mat 𝕋 n n) : Bool :=
  !(List.finRange n).all fun a => (List.finRange n).all fun b => le (Q a b) zero && le zero (Q a b)

/-- Whether coordinate `i` of every generator of `Z` is certified zero. -/
@[step_of Zonotope.quadMapTriFiltered]
def Zonotope.step_quadMapTriFilteredZeroRow (Z : Zonotope (Vec 𝕋 m)) (i : Fin m) : Bool :=
  (List.finRange Z.h).all fun j => le (Z.G j i) zero && le zero (Z.G j i)

/-- The box of `Z` as one generator: the absolute row sums, `0` in the certified zero rows. -/
@[step_of Zonotope.quadMapTriFiltered]
def Zonotope.step_quadMapTriFilteredBox (Z : Zonotope (Vec 𝕋 m)) : Zonotope (Vec 𝕋 m) where
  h := 1
  c := Z.c
  G := fun _ i =>
    if Z.step_quadMapTriFilteredZeroRow i then zero else sumUp fun j => absolute (Z.G j i)
  I_error := Z.I_error


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `quadMap` of a zonotope with its `nonzeroFilter`, or its box for one nonzero output. -/
def Zonotope.quadMapTriFiltered (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  let Zq := Z.quadMapTri Q                                          -- aux_quadMapSingle
  let used := (Finset.univ.filter fun i => Zonotope.step_quadMapTriFilteredUsed (Q i) = true).card
  let rows := (Finset.univ.filter fun i => Zq.step_quadMapTriFilteredZeroRow i = false).card
  if used ≤ 1 ∧ rows ≤ 1 then Zq.step_quadMapTriFilteredBox                -- sum(abs(Gquad),2)
  else Zq.compactZeros                                              -- nonzeroFilter(Gquad)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
