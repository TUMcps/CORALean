module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LinearSys.verifyBoxDotUpFloat`, the dot product with a box along a perturbed direction

An upper bound of `ℓ' Σ_c x_c` for every matrix `x` in the box `X` and every direction `ℓ` whose
weighted error from the float `ℓ̃` is at most `E`: each `ℓ̃_l x_lc` below the larger corner, rounded
up, and the error `E β` with `β` a bound of the scaled row sums `Σ_c |x_lc| / s_l`. For one column,
the support of the constant input's solution `w` (CORA's `l' Pu`) and of its curvature term
`G u₀` along the propagated direction.

## Inputs
* `X` – float box
* `β` – float bound of the scaled row sums of the box
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float upper bound of `ℓ' Σ_c x_c` over the box
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

/-- `Σ_c Σ_l max(ℓ̃_l X.inf_lc, ℓ̃_l X.sup_lc) + E β`, rounded up. -/
def LinearSys.verifyBoxDotUpFloat (X : Interval (Mat 𝕋 n k)) (β : 𝕋) (ℓ : Vec 𝕋 n) (E : 𝕋) : 𝕋 :=
  addUp (sumUp fun c => sumUp fun l => maximum (mulUp (ℓ l) (X.inf l c)) (mulUp (ℓ l) (X.sup l c)))
    (mulUp E β)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
