module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.OneParamF
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The powers of a one-parameter matrix, by the coefficients of `β`

The first step of the proof of [1, Thm. 1]: `(C + βG)ⁱ = D_i + Σ_{l=1}^i βˡ F_i^{(l)}` for every
`β`, by induction on `i`, multiplying on the right by `C + βG`. Internally `D_i` and the
`F_i^{(l)}` are one family `P_i^{(l)}` (`D_i` at `l = 0`), which vanishes for `l > i`; then the
three printed rules for `F_{i+1}^{(l)}` are the single rule `P_i^{(l-1)} G + P_i^{(l)} C`.

## Inputs
* `C` – center matrix
* `G` – generator matrix
* `β` – generator weight
* `i` – power

## Hypotheses
* none

## Conclusion
* the power is a polynomial in the weight with the stated coefficients

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `F_i^{(l)}` vanishes outside `1 ≤ l ≤ i`. -/
private theorem aux_oneParamF_eq_zero (C G : Mat ℝ n n) :
    ∀ i l, (l = 0 ∨ i < l) → MatExp.oneParamF C G i l = 0
  | 0, _, _ => rfl
  | i + 1, l, h => by
    rw [MatExp.oneParamF, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The printed rules as one: `F_{i+1}^{(l)} = P_i^{(l-1)} G + P_i^{(l)} C` for `l ≥ 1`. -/
private theorem aux_oneParamF_succ (C G : Mat ℝ n n) (i l : ℕ) (hl : 1 ≤ l) : -- --- CONCL ---
    MatExp.oneParamF C G (i + 1) l =
      (if l - 1 = 0 then MatExp.oneParamD C i else MatExp.oneParamF C G i (l - 1)) * G +
        (if l = 0 then MatExp.oneParamD C i else MatExp.oneParamF C G i l) *
          C := by -- --- PROOF ---
  rw [MatExp.oneParamF, if_neg (by omega : l ≠ 0)]
  by_cases h1 : l = 1
  · subst h1; rw [if_pos rfl, if_pos rfl]
  rw [if_neg h1, if_neg (by omega : l - 1 ≠ 0)]
  by_cases h2 : 2 ≤ l ∧ l < i + 1
  · rw [if_pos h2]
  rw [if_neg h2]
  by_cases h3 : l = i + 1
  · -- the top coefficient: `F_i^{(i+1)} = 0`
    subst h3
    rw [if_pos rfl, aux_oneParamF_eq_zero C G i (i + 1) (Or.inr (by omega)), zero_mul,
      add_zero, Nat.add_sub_cancel]
  · -- past the top: both vanish
    rw [if_neg h3, aux_oneParamF_eq_zero C G i (l - 1) (Or.inr (by omega)),
      aux_oneParamF_eq_zero C G i l (Or.inr (by omega)), zero_mul, zero_mul, add_zero]

/-- `(C + βG)ⁱ = Σ_{l=0}^i βˡ P_i^{(l)}`. -/
private theorem aux_pow_eq_sum_range (C G : Mat ℝ n n) (β : ℝ) (i : ℕ) : -- --- CONCL ---
    (C + β • G) ^ i = ∑ l ∈ Finset.range (i + 1), β ^ l •
      (if l = 0 then MatExp.oneParamD C i else MatExp.oneParamF C G i l) := by -- --- PROOF ---
  induction i with
  | zero => simp [MatExp.oneParamD]
  | succ i ih =>
    set P := fun l => if l = 0 then MatExp.oneParamD C i else MatExp.oneParamF C G i l with hP
    -- the new coefficients from the old
    have hnew : ∀ l, (if l + 1 = 0 then MatExp.oneParamD C (i + 1)
        else MatExp.oneParamF C G (i + 1) (l + 1)) = P l * G + P (l + 1) * C := fun l => by
      rw [if_neg (by omega), aux_oneParamF_succ C G i (l + 1) (by omega), Nat.add_sub_cancel]
    have htop : P (i + 1) = 0 := by
      simp only [hP]
      rw [if_neg (by omega), aux_oneParamF_eq_zero C G i (i + 1) (Or.inr (by omega))]
    rw [pow_succ, ih, Finset.sum_range_succ' _ (i + 1), if_pos rfl, pow_zero, one_smul]
    simp only [hnew, smul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_add, smul_mul_assoc,
      mul_smul_comm]
    rw [show MatExp.oneParamD C (i + 1) = P 0 * C by simp [hP, MatExp.oneParamD],
      Finset.sum_range_succ' (fun l => β ^ l • (P l * C)), Finset.sum_range_succ
        (fun l => β ^ (l + 1) • (P (l + 1) * C)), htop, zero_mul, smul_zero, add_zero, pow_zero,
      one_smul]
    rw [Finset.smul_sum]
    simp only [smul_smul, ← pow_succ']
    abel

/-- `Σ_{l=1}^i f l = Σ_{l=0}^{i-1} f (l + 1)`. -/
private theorem aux_sum_Icc_one {M : Type} [AddCommMonoid M] (f : ℕ → M) (i : ℕ) :
    ∑ l ∈ Finset.Icc 1 i, f l = ∑ l ∈ Finset.range i, f (l + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], first step of the proof: `(C + βG)ⁱ = D_i + Σ_{l=1}^i βˡ F_i^{(l)}`. -/
theorem MatExp.oneParam_pow_eq (C G : Mat ℝ n n) (β : ℝ) (i : ℕ) :
    (C + β • G) ^ i = MatExp.oneParamD C i +
      ∑ l ∈ Finset.Icc 1 i, β ^ l • MatExp.oneParamF C G i l := by
  rw [aux_pow_eq_sum_range, Finset.sum_range_succ', if_pos rfl, pow_zero, one_smul,
    aux_sum_Icc_one (fun l => β ^ l • MatExp.oneParamF C G i l), add_comm]
  simp only [Nat.add_one_ne_zero, if_false]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
