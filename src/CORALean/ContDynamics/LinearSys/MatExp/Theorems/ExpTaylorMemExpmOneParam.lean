import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmOneParam
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.OneParamSumPowEq
import CORALean.ContSet.Zonotope.Real.Theorems.OfOneParamPolyContains

/-!
# The Taylor polynomial of every member lies in `MatExp.expmOneParam`

The core of [1, Thm. 1]: for every `β ∈ [-1, 1]`, `Σ_{i=0}^η ((C + βG) r)ⁱ/i!` is a point of
`K(r)`. By `MatExp.oneParam_sum_pow_eq` the polynomial is `Σ_l βˡ G̃_K^{(l)}` with
`G̃_K^{(0)} = Σ_i D_i rⁱ/i!` and `G̃_K^{(l)} = Σ_{i=l}^η F_i^{(l)} rⁱ/i!`,
and `K(r)` is `Zonotope.ofOneParamPoly` of these coefficients, whose containment is the halving
of the even powers.

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `K(r)` is the polynomial zonotope of the coefficients `G̃_K^{(l)}`. -/
theorem aux_expmOneParam_eq (C G : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    MatExp.expmOneParam C G r η = Zonotope.ofOneParamPoly (fun l => if l = 0 then
      ∑ i ∈ Finset.range (η + 1), (r ^ i / i.factorial) • MatExp.oneParamD C i
      else ∑ i ∈ Finset.Icc l η, (r ^ i / i.factorial) • MatExp.oneParamF C G i l)
      η := by -- --- PROOF ---
  simp only [MatExp.expmOneParam, Zonotope.ofOneParamPoly]
  congr 1
  · -- the centre: an even index is never odd, and never `0` from `l ≥ 1`
    rw [if_pos trivial]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl1 : 1 ≤ l := (Finset.mem_Icc.1 hl).1
    rw [if_neg (Nat.not_odd_iff_even.2 (even_two_mul l)), if_neg (by omega)]

/-- The Taylor polynomial, by the powers of `β` (`MatExp.oneParam_sum_pow_eq` at `rⁱ/i!`). -/
theorem aux_expTaylor_oneParam (C G : Mat ℝ n n) (r β : ℝ) (η : ℕ) :
    MatExp.expTaylor (r • (C + β • G)) η = ∑ k ∈ Finset.range (η + 1), β ^ k •
      (if k = 0 then ∑ i ∈ Finset.range (η + 1), (r ^ i / i.factorial) • MatExp.oneParamD C i
      else ∑ i ∈ Finset.Icc k η, (r ^ i / i.factorial) • MatExp.oneParamF C G i k) := by
  rw [← MatExp.oneParam_sum_pow_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_pow, smul_smul, inv_mul_eq_div]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the Taylor polynomial of `e^{(C + βG) r}` lies in `K(r)` for every `β`. -/
theorem MatExp.expTaylor_mem_expmOneParam (C G : Mat ℝ n n) (r : ℝ) (η : ℕ) {β : ℝ}
    (hβ : |β| ≤ 1) :
    MatExp.expTaylor (r • (C + β • G)) η ∈ (MatExp.expmOneParam C G r η).construct := by
  rw [aux_expmOneParam_eq, aux_expTaylor_oneParam]
  exact Zonotope.ofOneParamPoly_contains _ η hβ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
