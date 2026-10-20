module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.containsPoint`, over a floating-point scalar

CORA's `@spectraShadow/contains_` for a point solves a semidefinite program for the variables
`β`. A float solve is not exact, so here the solve is the caller's and only its result is
checked: the stored matrices are symmetric (`le` both ways), the combination
`A₀ + Σ βₗ Aₗ`, each entry between its two roundings, is diagonally dominant (its diagonal's
lower bound at least the rounded-up sum of the off-diagonal magnitudes), which makes it
positive semidefinite, and the remainder `p - c - G β`, bracketed by directed roundings, lies in
the error box. Only `true` is certain; a combination that is semidefinite but not diagonally
dominant answers `false`.

## Inputs
* `S` – spectrahedral shadow
* `p` – point of length `n`
* `β` – vector of length `S.m`

## Output
* `true` when the combination `A₀ + Σ βₗ Aₗ` is certified positive semidefinite and gives `p`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.containsPoint (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (p : Vec 𝕋 n)
    (β : Vec 𝕋 S.m) : Bool :=
  -- each entry of `A₀ + Σ βₗ Aₗ` between its two roundings, and its magnitude
  let entryLo : Fin S.k → Fin S.k → 𝕋 := fun i j =>
    addDown (S.A₀ i j) (dotDown β fun l => S.A l i j)
  let entryHi : Fin S.k → Fin S.k → 𝕋 := fun i j =>
    addUp (S.A₀ i j) (dotUp β fun l => S.A l i j)
  let mag : Fin S.k → Fin S.k → 𝕋 := fun i j => maximum (entryHi i j) (neg (entryLo i j))
  let offDiag : Fin S.k → 𝕋 := fun i => sumUp fun j => if j = i then zero else mag i j
  let symmetric : Bool := (List.finRange S.k).all fun i => (List.finRange S.k).all fun j =>
    le (S.A₀ i j) (S.A₀ j i) && (List.finRange S.m).all fun l => le (S.A l i j) (S.A l j i)
  let dominant : Bool := (List.finRange S.k).all fun i => le (offDiag i) (entryLo i i)
  -- the remainder `p - c - G β`, between its two roundings
  let lo : Vec 𝕋 n := fun r => subDown (p r) (addUp (S.c r) (dotUp (fun j => S.G j r) β))
  let hi : Vec 𝕋 n := fun r => subUp (p r) (addDown (S.c r) (dotDown (fun j => S.G j r) β))
  symmetric && dominant &&
    (List.finRange n).all fun r => le (S.I_error.inf r) (lo r) && le (hi r) (S.I_error.sup r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
