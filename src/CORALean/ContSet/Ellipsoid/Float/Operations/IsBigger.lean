module

public import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# `Ellipsoid.isBigger`, over a floating-point scalar

CORA's `@ellipsoid/isBigger` (`E₂` fits into `E₁` up to the centers) compares the shape matrices
by a simultaneous diagonalisation, which rounding cannot decide. A sound test instead checks a
caller-proposed factor `T` with `G₂ ≈ G₁ T`: its Frobenius norm at most `1` (so `T u` stays in
the unit ball), and the residual `G₂ - G₁ T`, bracketed by directed roundings, together with
`E₂`'s error box inside `E₁`'s (the residual's reach bounded by `generatorError`). Only `true` is
certain.
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

def Ellipsoid.isBigger (E₁ E₂ : Ellipsoid 𝕋 n) (T : Mat 𝕋 E₁.k E₂.k) : Bool :=
  -- the residual `G₂ - G₁ T` between its two roundings, and its magnitude
  let lo : Mat 𝕋 n E₂.k := fun i j =>
    subDown (E₂.G i j) (dotUp (fun l => E₁.G i l) fun l => T l j)
  let hi : Mat 𝕋 n E₂.k := fun i j =>
    subUp (E₂.G i j) (dotDown (fun l => E₁.G i l) fun l => T l j)
  let gap : Mat 𝕋 n E₂.k := fun i j => maximum (hi i j) (neg (lo i j))
  let reach : Vec 𝕋 n := radius gap
  le (sumUp fun i => sqSumUp fun j => absolute (T i j)) one &&
    (List.finRange n).all fun i =>
      le (E₁.I_error.inf i) (subDown (E₂.I_error.inf i) (reach i)) &&
        le (addUp (E₂.I_error.sup i) (reach i)) (E₁.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
