module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputOneParam
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.OneParamSumPowEq
public import CORALean.ContSet.Zonotope.Real.Theorems.OfOneParamPolyContains
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# `MatExp.inputOneParam` holds the partial input solution's Taylor part

[1, Sec. IV-B]: for every `β ∈ [-1, 1]`,
`Σ_{i=0}^η (C + βG)ⁱ (c_c + β g_c) r^{i+1}/(i+1)!` is a point of the zonotope: the matrix
polynomial by the powers of `β` (`MatExp.oneParam_sum_pow_eq`), applied to `c_c + β g_c`, is a
polynomial of degree `η + 1` with the coefficients `w_k`, and `Zonotope.ofOneParamPoly_contains`
encloses it. The remainder `∫ E(r) dt c(β) ⊆ E(r) r c(β)` is [1]'s citation of Althoff's thesis
and is not part of this statement.

## Inputs
* `C` – center matrix
* `G` – generator matrix
* `c_c` – input center
* `g_c` – input generator
* `r` – step length
* `η` – Taylor order
* `β` – generator weight

## Hypotheses
* `hβ` – weight within one in magnitude

## Conclusion
* the partial input solution's Taylor part lies in the zonotope

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". 2012 American Control Conference (ACC), 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.inputOneParam_contains (C G : Mat ℝ n n) (c_c g_c : Vec ℝ n) (r : ℝ) (η : ℕ)
    {β : ℝ} (hβ : |β| ≤ 1) : -- --- CONCL ---
    ∑ i ∈ Finset.range (η + 1), (r ^ (i + 1) / (i + 1).factorial) •
        ((C + β • G) ^ i *ᵥ (c_c + β • g_c)) ∈
      (MatExp.inputOneParam C G c_c g_c r η).construct := by -- --- PROOF ---
  set a : ℕ → ℝ := fun i => r ^ (i + 1) / (i + 1).factorial with ha
  set u : ℕ → Mat ℝ n n := fun k =>
    if k = 0 then ∑ i ∈ Finset.range (η + 1), a i • MatExp.oneParamD C i
    else ∑ i ∈ Finset.Icc k η, a i • MatExp.oneParamF C G i k with hu
  -- the matrix polynomial by the powers of `β`, then `c(β)` applied
  have hsum : ∑ i ∈ Finset.range (η + 1), a i • ((C + β • G) ^ i *ᵥ (c_c + β • g_c)) =
      ∑ k ∈ Finset.range (η + 1), β ^ k • (u k *ᵥ c_c) +
        ∑ k ∈ Finset.range (η + 1), β ^ (k + 1) • (u k *ᵥ g_c) := by
    calc _ = (∑ i ∈ Finset.range (η + 1), a i • (C + β • G) ^ i) *ᵥ (c_c + β • g_c) := by
          rw [Matrix.sum_mulVec]
          exact Finset.sum_congr rfl fun i _ => (Matrix.smul_mulVec _ _ _).symm
      _ = (∑ k ∈ Finset.range (η + 1), β ^ k • u k) *ᵥ (c_c + β • g_c) := by
          rw [MatExp.oneParam_sum_pow_eq]
      _ = _ := by
          rw [Matrix.sum_mulVec, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul,
            ← pow_succ]
  -- the same, as one polynomial of degree `η + 1`
  have hw : ∑ k ∈ Finset.range (η + 1 + 1), β ^ k •
      ((if k < η + 1 then u k *ᵥ c_c else 0) + (if k = 0 then 0 else u (k - 1) *ᵥ g_c)) =
      ∑ k ∈ Finset.range (η + 1), β ^ k • (u k *ᵥ c_c) +
        ∑ k ∈ Finset.range (η + 1), β ^ (k + 1) • (u k *ᵥ g_c) := by
    simp only [smul_add, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ (fun k => β ^ k • if k < η + 1 then u k *ᵥ c_c else 0),
      Finset.sum_range_succ' (fun k => β ^ k • if k = 0 then 0 else u (k - 1) *ᵥ g_c),
      if_neg (lt_irrefl _), if_pos rfl, smul_zero, smul_zero, add_zero, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.1 hk)]
  rw [hsum, ← hw]
  exact Zonotope.ofOneParamPoly_contains _ (η + 1) hβ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
