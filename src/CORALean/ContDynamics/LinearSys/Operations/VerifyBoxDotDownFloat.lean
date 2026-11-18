module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LinearSys.verifyBoxDotDownFloat`, the dot product with a box from below

The counterpart of `LinearSys.verifyBoxDotUpFloat` from below: a lower bound of `ℓ' Σ_c x_c` for
every `x` in the box `X` and every direction within `E` of `ℓ̃`, each `ℓ̃_l x_lc` above the smaller
corner, rounded down, less `E β`. For one column, the constant input's solution in the lower
distance of the falsification.

## Inputs
* `X` – float box
* `β` – float bound of the scaled row sums of the box
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float lower bound of `ℓ' Σ_c x_c` over the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σ_c Σ_l min(ℓ̃_l X.inf_lc, ℓ̃_l X.sup_lc) − E β`, rounded down. -/
def LinearSys.verifyBoxDotDownFloat (X : Interval (Mat 𝕋 n k)) (β : 𝕋) (ℓ : Vec 𝕋 n)
    (E : 𝕋) : 𝕋 :=
  subDown (sumDown fun c => sumDown fun l =>
    minimum (mulDown (ℓ l) (X.inf l c)) (mulDown (ℓ l) (X.sup l c))) (mulUp E β)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
