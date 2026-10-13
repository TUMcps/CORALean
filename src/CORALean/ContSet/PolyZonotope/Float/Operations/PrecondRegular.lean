module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `PolyZonotope.precondRegular`

Certifies that a preconditioner `C`, an approximate inverse of `M` computed in the scalar's own
arithmetic and trusted for nothing, is nonsingular: every row of `|1 - M C|`, bounded above with
`M C` rounded both ways, sums to less than `1`. CORA takes `C = inv(df(x_))` and relies on
MATLAB's `inv`; the test it feeds proves a pre-image of `C y` only, so a singular `C` would prove
nothing about `y`, and this check is what replaces the trust in `inv`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every row of `|1 - M C|` sums to less than `1`, so `C` is injective. -/
def PolyZonotope.precondRegular (M C : Mat 𝕋 n n) : Bool :=
  -- `M C`, rounded both ways
  let lo := matMulDown M C
  let hi := matMulUp M C
  -- an upper bound of `|(1 - M C)ᵢⱼ|`
  let r : Fin n → Fin n → 𝕋 := fun i j =>
    maximum (absolute (subDown (if i = j then one else zero) (hi i j)))
      (absolute (subUp (if i = j then one else zero) (lo i j)))
  (List.finRange n).all fun i => ltStrict (sumUp (r i)) one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
