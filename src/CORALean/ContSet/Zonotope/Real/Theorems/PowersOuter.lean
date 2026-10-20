module

public import CORALean.ContSet.Zonotope.Real.Operations.Powers
public import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter

@[expose] public section

/-!
# `Zonotope.powers` encloses `M₀ * M ^ k` for every member

Induction on `k` against `matMul_outer`, with `M₀ * M ^ (k + 1) = (M₀ * M ^ k) * M`. The default
call of CORA (`P = Z`) is `M₀ := M`, giving `M ^ (k + 1)`; `expmMixed` starts at the dependent
square (`initialOrder = 2`), whose members are the squares `M * M`.

## Inputs
* `Z` – base matrix zonotope
* `P` – starting matrix zonotope
* `M` – matrix of the base
* `M₀` – matrix of the start
* `k` – exponent

## Hypotheses
* `hM` – `M` lies in `Z`
* `hM₀` – `M₀` lies in `P`

## Conclusion
* `M₀` times `M` to the `k` lies in the `k`-th power zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `k`-th entry of `powers Z P` contains `M₀ * M ^ k` for `M ∈ Z` and `M₀ ∈ P`. -/
theorem Zonotope.powers_outer (Z P : Zonotope (Mat ℝ n n)) {M M₀ : Mat ℝ n n}
    (hM : M ∈ Z.construct) (hM₀ : M₀ ∈ P.construct) (k : ℕ) : -- --- CONCL ---
    M₀ * M ^ k ∈ (Zonotope.powers Z P k).construct := by -- --- PROOF ---
  induction k with
  | zero => rw [pow_zero, mul_one]; exact hM₀
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    exact Zonotope.matMul_outer _ Z (Set.mem_iUnion₂.mpr ⟨_, ih, Set.mem_image_of_mem _ hM⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
