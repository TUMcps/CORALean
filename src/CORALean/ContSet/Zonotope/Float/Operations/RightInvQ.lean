module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.rightInvQ`

An upper bound on the largest absolute row sum of `1 - G H`, rounded up: the certificate that a
candidate right inverse `H` is good enough (`Zonotope.rightInv_reach`) when it is at most one half.

## Inputs
* `G` – generator matrix
* `H` – candidate right inverse

## Output
* upper bound on the largest row sum of the residual
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

@[step_of Zonotope.rightInvQ]
def Zonotope.step_rightInvResidual (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) : Fin n → Fin n → 𝕋 := fun i j =>
  maximum
    (absolute (subDown (if i = j then one else zero) (dotUp (fun l => G i l) fun l => H l j)))
    (absolute (subUp (if i = j then one else zero) (dotDown (fun l => G i l) fun l => H l j)))


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.rightInvQ (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) : 𝕋 :=
  maximumOver fun i => sumUp fun j => Zonotope.step_rightInvResidual G H i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
