module

public import CORALean.ContSet.Zonotope.Float.Operations.CompactZeros
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.quadMapFilter`, over a floating-point scalar

The last step of CORA's `@zonotope/quadMap`, for one zonotope or two: where two or more of the
`Q⁽ⁱ⁾` are nonzero, CORA's `nonzeroFilter` (`compactZeros`); where at most one is, the box of the
generators, one generator of the absolute row sums (`sumUp`). The box is taken only where at most
one coordinate of the generators is not certified zero, so that it is the segment along that
coordinate; otherwise `compactZeros` keeps the set. At most one nonzero `Q⁽ⁱ⁾` leaves the other
rows zero at `nearest`, where this is CORA's choice. Both branches hold the set
(`quadMapFilter_outer`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Zq` – zonotope of the outputs, as the quadratic map computed it

## Output
* zonotope with CORA's generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   20-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Whether `Q` has an entry that is not certified zero (CORA's `any(Q{i}(:))`). -/
@[step_of Zonotope.quadMapFilter]
def Zonotope.step_quadMapFilterUsed (Q : Mat 𝕋 n n) : Bool :=
  !(List.finRange n).all fun a => (List.finRange n).all fun b => le (Q a b) zero && le zero (Q a b)

/-- Whether coordinate `i` of every generator of `Z` is certified zero. -/
@[step_of Zonotope.quadMapFilter]
def Zonotope.step_quadMapFilterZeroRow (Z : Zonotope (Vec 𝕋 m)) (i : Fin m) : Bool :=
  (List.finRange Z.h).all fun j => le (Z.G j i) zero && le zero (Z.G j i)

/-- The box of `Z` as one generator: the absolute row sums, `0` in the certified zero rows. -/
@[step_of Zonotope.quadMapFilter]
def Zonotope.step_quadMapFilterBox (Z : Zonotope (Vec 𝕋 m)) : Zonotope (Vec 𝕋 m) where
  h := 1
  c := Z.c
  G := fun _ i => if Z.step_quadMapFilterZeroRow i then zero else sumUp fun j => absolute (Z.G j i)
  I_error := Z.I_error


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `nonzeroFilter` of a quadratic map's outputs, or their box for one nonzero output. -/
def Zonotope.quadMapFilter (Q : Fin m → Mat 𝕋 n n) (Zq : Zonotope (Vec 𝕋 m)) :
    Zonotope (Vec 𝕋 m) :=
  let used := (Finset.univ.filter fun i => Zonotope.step_quadMapFilterUsed (Q i) = true).card
  let rows := (Finset.univ.filter fun i => Zq.step_quadMapFilterZeroRow i = false).card
  if used ≤ 1 ∧ rows ≤ 1 then Zq.step_quadMapFilterBox                  -- sum(abs(Gquad),2)
  else Zq.compactZeros                                              -- nonzeroFilter(Gquad)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
