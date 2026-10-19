module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.isequal`, over a floating-point scalar

The test at tolerance `0`, as over ℝ: the shape matrix, the center and the two ends of the error
box equal entry by entry, each by the certified `le` in both directions. Certified in one
direction only: `true` is a proof, `false` refutes nothing.

## Inputs
* `E` – ellipsoid
* `S` – ellipsoid

## Output
* `true` only if shape, center and error box agree entrywise
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.isequal (E S : Ellipsoid 𝕋 n) : Bool :=
  (List.finRange n).all (fun i =>
    (le (E.q i) (S.q i) && le (S.q i) (E.q i)) &&
    (le (E.I_error.inf i) (S.I_error.inf i) && le (S.I_error.inf i) (E.I_error.inf i)) &&
    (le (E.I_error.sup i) (S.I_error.sup i) && le (S.I_error.sup i) (E.I_error.sup i)) &&
    (List.finRange n).all fun j => le (E.Q i j) (S.Q i j) && le (S.Q i j) (E.Q i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
