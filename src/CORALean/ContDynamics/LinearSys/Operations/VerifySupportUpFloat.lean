module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `LinearSys.verifySupportUpFloat`, the support of the initial set along a perturbed direction

CORA's `priv_verifyRA_supportFunc` evaluates the support of the zonotope `X₀ = ⟨c, G⟩` along the
propagated direction `ℓ_k` as `ℓ_k'c + Σⱼ |ℓ_k' gⱼ|`. The float direction `ℓ̃` is not `ℓ_k`; with a
bound `E` on `Σᵢ |ℓ_k − ℓ̃|ᵢ sᵢ` and `β` on every `|xᵢ|/sᵢ` over `X₀`, the support along `ℓ_k` is
at most CORA's value at `ℓ̃`, rounded up, plus `E β`. Each `|ℓ̃' gⱼ|` is bounded by the larger
magnitude of its sums rounded up and down, which at `nearest` are one number.

## Inputs
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `β` – float bound of the scaled entries of the initial set
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float upper bound of the support of `X₀` along the exact direction
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

/-- `ℓ̃'c + Σⱼ |ℓ̃' gⱼ| + E β`, rounded up. -/
def LinearSys.verifySupportUpFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m) (β : 𝕋) (ℓ : Vec 𝕋 n)
    (E : 𝕋) : 𝕋 :=
  let g := fun j => maximum (absolute (dotUp ℓ fun i => G i j))   -- ≥ |ℓ̃' gⱼ|
    (absolute (dotDown ℓ fun i => G i j))
  addUp (addUp (dotUp ℓ c) (sumUp g)) (mulUp E β)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
