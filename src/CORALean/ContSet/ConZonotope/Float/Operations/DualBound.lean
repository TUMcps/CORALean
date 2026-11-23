module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `ConZonotope.dualBound` over a floating-point scalar

The weak-duality bound `-‖w + Cᵀ λ‖₁ - λᵀ d` at the multipliers clamped at zero, rounded so that
it stays below `wᵀ β`: `w + Cᵀ λ` in both directions and the larger absolute value of the two,
the sums rounded up, the difference down. Then at least the bound at `λ = 0`, `-‖w‖₁`. In
CORA.cpp's order (`priv_dual_lower`'s certificate): `λ C` as one product, `w` added, the absolute
values summed, negated, less the sum of `λ d`, and the larger of that and `-‖w‖₁`. At round to
nearest the two roundings agree and the bound is CORA.cpp's bit for bit.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `w` – coefficients of the bounded form
* `lam` – multipliers

## Output
* the lower bound at the multipliers
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The larger of `-‖w + Cᵀ λ⁺‖₁ - λ⁺ᵀ d` and `-‖w‖₁`, rounded down. -/
def ConZonotope.dualBound (C : Mat 𝕋 p q) (d : Vec 𝕋 p) (w : Vec 𝕋 q) (lam : Vec 𝕋 p) : 𝕋 :=
  -- 1. the multipliers at least zero
  let μ : Vec 𝕋 p := fun i => maximum (lam i) zero
  -- 2. `w + Cᵀ μ`, rounded up and down
  let sUp : Vec 𝕋 q := fun j => addUp (w j) (sumUp fun i => mulUp (μ i) (C i j))
  let sDown : Vec 𝕋 q := fun j => addDown (w j) (sumDown fun i => mulDown (μ i) (C i j))
  -- 3. the bound at `μ`, each coefficient at the larger absolute value of its two roundings
  let atMu := subDown (neg (sumUp fun j => maximum (absolute (sUp j)) (absolute (sDown j))))
    (sumUp fun i => mulUp (μ i) (d i))
  -- 4. at least the bound at zero
  maximum atMu (neg (sumUp fun j => absolute (w j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
