module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Taylm.accumTerm`

One term `c · tᵉ` added into a term list kept sorted by its exponents, lexicographically, as
CORA.cpp's `terms[e] += c` adds it into its ordered map: the coefficient of an equal exponent
becomes the sum, a new exponent enters at its place with `zero + c`. The sum is stored rounded
up; the second component bounds what that costs, the width of the sum between its two roundings.

## Inputs
* `L` – term list, sorted by exponents
* `c` – coefficient of the new term
* `e` – exponents of the new term

## Output
* the term list with the term added, and a bound of the rounding of the one addition
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.accumTerm (L : List (𝕋 × (Fin n → ℕ))) (c : 𝕋) (e : Fin n → ℕ) :
    List (𝕋 × (Fin n → ℕ)) × 𝕋 :=
  match L with
  | [] => ([(addUp zero c, e)], subUp (addUp zero c) (addDown zero c))
  | a :: L =>
    -- the exponents equal: the sum; before `a`: a new term; after it: further down the list
    if a.2 = e then ((addUp a.1 c, e) :: L, subUp (addUp a.1 c) (addDown a.1 c))
    else if decide (List.ofFn e < List.ofFn a.2) then
      ((addUp zero c, e) :: a :: L, subUp (addUp zero c) (addDown zero c))
    else
      let r := Taylm.accumTerm L c e
      (a :: r.1, r.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
