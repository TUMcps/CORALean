module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.DependentTermsOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FoldlPlusMem
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowersIntSqMem
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorTwo
public import CORALean.ContSet.Interval.Real.Theorems.PowersOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# `MatExp.expmTerms` encloses the Taylor sum of every member

The terms of order zero to two are `H`: the scaled member `M / r` at step `r` has
`I + (M/r) r + ½ (M/r)² r² = I + M + ½ M²`, the square of `M` is in the scaled-back exact square,
and the later terms are the right-multiplied powers from it (`powers_outer`), added one at a time
(`foldl_plus_mem`).

## Inputs
* `A` – interval matrix
* `r` – step length
* `k` – order offset
* `M` – member matrix

## Hypotheses
* `hr` – step length nonzero
* `hM` – member lies in the interval matrix

## Conclusion
* the member's Taylor sum lies in the terms enclosure
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

/-- The Taylor sum `Σ_{i ≤ k+2} Mⁱ/i!` of order `k + 2` is in `expmTerms` of that order. -/
theorem MatExp.expmTerms_mem (A : Interval (Mat ℝ n n)) {r : ℝ} (hr : r ≠ 0) (k : ℕ)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    MatExp.expTaylor M (k + 2) ∈ (MatExp.expmTerms A r (k + 2)).construct := by -- --- PROOF ---
  -- the member scaled by `1 / r` is in the scaled box, and `dependentTerms` encloses its terms
  have hM' : r⁻¹ • M ∈ (Interval.smul (1 / r) A).construct := by
    have h := Interval.smul_outer (1 / r) A hM
    simpa only [one_div] using h
  have hH := (MatExp.dependentTerms_outer (Interval.smul (1 / r) A) r hM').2
  have hT2 : 1 + MatExp.expW (r⁻¹ • M) r = MatExp.expTaylor M 2 := by
    rw [← MatExp.expTaylor_two, smul_smul, mul_inv_cancel₀ hr, one_smul]
  -- the powers `iPow{i}` enclose `M ^ i`, starting from the exact square
  have hpow : ∀ j, 3 ≤ j → M ^ j ∈ (Interval.powers A
      (MatExp.dependentTerms (Interval.smul (1 / r) A) r).intSq (j - 2)).construct :=
    fun j hj => MatExp.powers_intSq_mem A hr hM (by omega)
  -- the Taylor terms `3 … k + 2`, added to `H`, enclose the partial sum
  have hfold := MatExp.foldl_plus_mem
    (fun i => Interval.smul ((Nat.factorial i : ℝ)⁻¹) (Interval.powers A
      (MatExp.dependentTerms (Interval.smul (1 / r) A) r).intSq (i - 2)))
    (fun i => ((Nat.factorial i : ℝ)⁻¹) • M ^ i) 3 k
    (fun j _ => Interval.smul_outer _ _ (hpow (3 + j) (by omega))) hH
  rw [hT2] at hfold
  -- and the series splits as that partial sum
  have hsplit : MatExp.expTaylor M (k + 2) = MatExp.expTaylor M 2
      + ∑ j ∈ Finset.range k, ((Nat.factorial (3 + j) : ℝ)⁻¹) • M ^ (3 + j) := by
    unfold MatExp.expTaylor
    rw [show k + 2 + 1 = 3 + k by omega, Finset.sum_range_add]
  rw [hsplit]
  simpa only [MatExp.expmTerms, Nat.add_sub_cancel] using hfold

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
