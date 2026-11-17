module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `LinearSys.verifySupportDownFloat`, a lower bound of the support along a perturbed direction

The counterpart of `LinearSys.verifySupportUpFloat` from below, for CORA's falsification: the
support of `X₀ = ⟨c, G⟩` along the exact direction `ℓ_k` is attained at `c + G sign(ℓ_k' G)` and is
at least `ℓ̃'c + Σⱼ |ℓ̃' gⱼ| − E β`, each `|ℓ̃' gⱼ|` bounded below by the mignitude of its sums
rounded down and up.

## Inputs
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `β` – float bound of the scaled entries of the initial set
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float lower bound of the support of `X₀` along the exact direction
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ℓ̃'c + Σⱼ |ℓ̃' gⱼ| − E β`, rounded down. -/
def LinearSys.verifySupportDownFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m) (β : 𝕋) (ℓ : Vec 𝕋 n)
    (E : 𝕋) : 𝕋 :=
  let g := fun j => maximum zero (maximum (dotDown ℓ fun i => G i j)   -- ≤ |ℓ̃' gⱼ|
    (neg (dotUp ℓ fun i => G i j)))
  subDown (addDown (dotDown ℓ c) (sumDown g)) (mulUp E β)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
