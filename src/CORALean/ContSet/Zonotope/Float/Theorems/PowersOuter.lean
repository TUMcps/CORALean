module

public import CORALean.ContSet.Zonotope.Float.Operations.Powers
public import CORALean.ContSet.Zonotope.Float.Theorems.MatMulOuter

@[expose] public section

/-!
# `Zonotope.powers` contains the matrix powers

Each power is the rounded product of the previous one with `Z`, so `M₀ * M ^ k` stays inside by
`Zonotope.matMul_outer`.

## Inputs
* `Z` – matrix zonotope
* `P` – initial power
* `M` – member of `Z`
* `M₀` – member of `P`
* `k` – offset

## Hypotheses
* `hM` – `M` lies in `Z`
* `hM₀` – `M₀` lies in `P`

## Conclusion
* `M₀ * M ^ k` lies in the power at offset `k`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.powers_outer (Z P : Zonotope (Mat 𝕋 n n)) {M M₀ : Mat ℝ n n}
    (hM : M ∈ Z.construct) (hM₀ : M₀ ∈ P.construct) (k : ℕ) : -- --- CONCL ---
    M₀ * M ^ k ∈ (Zonotope.powers Z P k).construct := by -- --- PROOF ---
  induction k with
  | zero => rw [pow_zero, mul_one]; exact hM₀
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    exact Zonotope.matMul_outer _ Z (Set.mem_iUnion₂.mpr ⟨_, ih, Set.mem_image_of_mem _ hM⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
