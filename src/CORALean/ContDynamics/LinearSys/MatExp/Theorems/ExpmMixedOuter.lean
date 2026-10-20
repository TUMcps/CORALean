module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmMixed
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpmTermsMem
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpmFromOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowersIntSqMem
public import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter

@[expose] public section

/-!
# `MatExp.expmMixed` encloses the two parts of the exponential series

For `2 ≤ k < η` the first part holds the Taylor sum of order `k` (`expmTerms_mem`) and the second
the rest of the series, `e^M - Σ_{i ≤ k} Mⁱ/i!` (`expmFrom_outer` from order `k + 1`, started at
`A * iPow{k} ∋ M * Mᵏ`, `powers_intSq_mem`). Their sum encloses `e^M`. CORA also runs `η ≤ k`,
where the remainder overlaps the term of order `k + 1`.

## Inputs
* `A` – interval matrix
* `r` – step length
* `k` – intermediate order
* `η` – Taylor order
* `M` – member matrix

## Hypotheses
* `hr` – step length nonzero
* `hk` – intermediate order at least two
* `hη` – intermediate order below the Taylor order
* `hM` – member lies in the interval matrix

## Conclusion
* the member's Taylor sum and series rest lie in the two parts
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The two parts of `expmMixed` hold the Taylor sum and the rest of the series of every member. -/
theorem MatExp.expmMixed_outer (A : Interval (Mat ℝ n n)) {r : ℝ} (hr : r ≠ 0) {k η : ℕ}
    (hk : 2 ≤ k) (hη : k < η) {M : Mat ℝ n n} (hM : M ∈ A.construct) : -- --- CONCL ---
    MatExp.expTaylor M k ∈ (MatExp.expmMixed A r k η).eI.construct ∧
      exp M - MatExp.expTaylor M k ∈
        (MatExp.expmMixed A r k η).eI2.construct := by -- --- PROOF ---
  -- the first part: the order-`k` Taylor sum
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨MatExp.expmTerms_mem A hr j hM, ?_⟩
  -- the second part: `A * iPow{k}` encloses `M ^ (k + 1)`, and `expTaylor M k` is the partial sum
  have hP : M ^ (j + 2 + 1) ∈ (Interval.matMul A (Interval.powers A
      (MatExp.dependentTerms (Interval.smul (1 / r) A) r).intSq (j + 2 - 2))).construct := by
    rw [pow_succ']
    exact Interval.matMul_outer _ _ hM (MatExp.powers_intSq_mem A hr hM (by omega))
  have h := MatExp.expmFrom_outer A _ (η := η) (k := j + 2 + 1) hη hM hP
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
