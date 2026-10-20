module

public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The exponential series split after `N` terms

`e^z = Σ_{j<N} zʲ/j! + φ_N(z)z^N`, `φ_N(z) = Σ_i zⁱ/(i + N)!` the series [1, Eq. 4.1] (4.1a):
the tail of the exponential series, `Σ_i z^{i+N}/(i + N)!`, with `z^N` factored out. The step
behind the explicit Taylor remainder of [1, Remark 2]. For `z` in any complete normed
ℝ-algebra; the tail series is summable, dominated by the exponential series.

## Inputs
* `𝔸` – normed algebra
* `z` – element
* `N` – split index

## Hypotheses
* none

## Conclusion
* the exponential is a partial sum plus a series factor times a power

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open NormedSpace


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Remark 2]'s step: `e^z = Σ_{j<N} zʲ/j! + φ_N(z)z^N`, `φ_N` the series (4.1a). -/
theorem Krylov.exp_eq_sum_add_phi_mul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (z : 𝔸) (N : ℕ) : -- --- CONCL ---
    exp z = ∑ j ∈ Finset.range N, ((Nat.factorial j : ℝ)⁻¹) • z ^ j +
      (∑' i : ℕ, ((Nat.factorial (i + N) : ℝ)⁻¹) • z ^ i) * z ^ N := by -- --- PROOF ---
  have hs := expSeries_summable' (𝕂 := ℝ) z
  -- the tail, dominated by the exponential series
  have ht : Summable fun i : ℕ => ((Nat.factorial (i + N) : ℝ)⁻¹) • z ^ i := by
    refine Summable.of_norm_bounded (norm_expSeries_summable' (𝕂 := ℝ) z) fun i => ?_
    rw [norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_add_right i N))
  rw [congrFun (exp_eq_tsum ℝ) z, ← hs.sum_add_tsum_nat_add N, ← ht.tsum_mul_right]
  congr 1
  refine tsum_congr fun i => ?_
  rw [smul_mul_assoc, pow_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
