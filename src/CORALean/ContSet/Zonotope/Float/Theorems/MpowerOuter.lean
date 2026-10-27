module

public import CORALean.ContSet.Zonotope.Float.Operations.Mpower
public import CORALean.ContSet.Zonotope.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MatPowOuter

@[expose] public section

/-!
# `Zonotope.mpower` contains the matrix powers

The zeroth power is the identity point, the first is the zonotope, and each next one is the
rounded product of the previous power with the zonotope, which `Zonotope.matMul_outer` encloses.

## Inputs
* `Z` – matrix zonotope
* `A` – member of `Z`
* `k` – exponent

## Hypotheses
* `hA` – `A` lies in `Z`

## Conclusion
* `A ^ k` lies in the `k`-th power
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

theorem Zonotope.mpower_outer (Z : Zonotope (Mat 𝕋 n n)) {A : Mat ℝ n n} (hA : A ∈ Z.construct)
    (k : ℕ) : -- --- CONCL ---
    A ^ k ∈ (Z.mpower k).construct := by -- --- PROOF ---
  rcases k with _ | k
  · -- the identity point is the zeroth power of `matPow`
    exact Zonotope.matPow_outer Z hA 0
  · induction k with
    | zero => rw [zero_add, pow_one]; exact hA
    | succ k ih =>
      rw [pow_succ]
      exact Zonotope.matMul_outer _ Z (Set.mem_iUnion₂.mpr ⟨_, ih, Set.mem_image_of_mem _ hA⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
