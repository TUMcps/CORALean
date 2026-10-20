module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow
public import CORALean.Global.Float.NoNaN
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `SpectraShadow.dualCertified`

The check of a dual certificate `Y` for the support of a shadow along `a`, the semidefinite
program CORA's `supportFunc_` solves: `Y` symmetric and diagonally dominant (so `⪰ 0`), checked
with `le` on stored entries, and the equalities `tr(Aᵢ Y) = -aᵀ Gᵢ` for every variable, which no
rounded arithmetic can confirm and which are therefore decided exactly in ℚ (`ToRat`). A solver's
`Y` rarely meets them exactly; the check is what makes its answer usable, not a way to find one.

## Inputs
* `S` – spectrahedral shadow
* `a` – vector of length `n`
* `Y` – `S.k × S.k` matrix

## Output
* `true` when `Y` is symmetric, dominant and meets `tr(Aᵢ Y) = -aᵀGᵢ`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps ToRat

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.dualCertified (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) (Y : Mat 𝕋 S.k S.k) :
    Bool :=
  -- `Y` symmetric and diagonally dominant, entry by entry
  let symmetric : Bool := (List.finRange S.k).all fun i => (List.finRange S.k).all fun j =>
    le (Y i j) (Y j i)
  let dominant : Bool := (List.finRange S.k).all fun i =>
    le (sumUp fun j => if j = i then zero else absolute (Y i j)) (Y i i)
  -- `tr(Aₗ Y) = -aᵀ Gₗ`, exactly
  let traceQ : Mat 𝕋 S.k S.k → ℚ := fun A => ∑ r, ∑ j, toRat (A r j) * toRat (Y j r)
  let target : Fin S.m → ℚ := fun l => -∑ r, toRat (a r) * toRat (S.G l r)
  let equalities : Bool := (List.finRange S.m).all fun l => decide (traceQ (S.A l) = target l)
  -- no NaN among the floats `toRat` reads: it would take it for the number `1.5 * 2 ^ 1024`
  let finite : Bool := noNaN (𝕋 := 𝕋) Y && noNaN (𝕋 := 𝕋) a && noNaN (𝕋 := 𝕋) S.G &&
    (List.finRange S.m).all fun l => noNaN (𝕋 := 𝕋) (S.A l)
  symmetric && dominant && equalities && finite

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
