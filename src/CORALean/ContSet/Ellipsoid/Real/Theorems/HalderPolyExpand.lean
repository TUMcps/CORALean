import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.HalderMu
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Halder's polynomial in the elementary symmetric polynomials

[1, Eq. 24]: the polynomial form `∑ᵢ (β² − 1/λᵢ) ∏_{j≠i} (β + 1/λⱼ)` of the stationarity equation
(22) is `d β^(d+1) + ∑_{r=1}^{d+1} µᵣ β^(d+1−r)`, `µᵣ = (d − r) eᵣ − (r − 1) eᵣ₋₁` of [1, Eq. 23]
and `e_{d+1} = 0`. For `P = ∏ (X + 1/λⱼ) = ∑ eₖ X^(d−k)` (Vieta) the sum is
`(X² + X) P' − d P`, as `∑ᵢ (X + 1/λᵢ) ∏_{j≠i} = d P` and `∑ᵢ ∏_{j≠i} = P'`. The printed (24)
counts the `r = 1` term twice (`printed_poly_counterexample`).

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Polynomial Finset

variable {ι : Type*} [Fintype ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_poly_identity [DecidableEq ι] (x : ι → ℝ) :
    ∑ i, (X ^ 2 - C (x i)) * ∏ j ∈ univ.erase i, (X + C (x j))
      = (X ^ 2 + X) * derivative (∏ j, (X + C (x j)))
        - C (Fintype.card ι : ℝ) * ∏ j, (X + C (x j)) := by -- --- PROOF ---
  have hP' : derivative (∏ j, (X + C (x j))) = ∑ i, ∏ j ∈ univ.erase i, (X + C (x j)) := by
    rw [derivative_prod_finset]
    refine sum_congr rfl fun i _ => ?_
    simp
  -- `∑ᵢ (X + xᵢ) ∏_{j≠i} = d · P`
  have hd : ∑ i, (X + C (x i)) * ∏ j ∈ univ.erase i, (X + C (x j))
      = C (Fintype.card ι : ℝ) * ∏ j, (X + C (x j)) := by
    have : ∀ i, (X + C (x i)) * ∏ j ∈ univ.erase i, (X + C (x j)) = ∏ j, (X + C (x j)) :=
      fun i => mul_prod_erase univ (fun j => X + C (x j)) (mem_univ i)
    simp_rw [this]
    simp [Finset.sum_const]
  have hx : ∑ i, C (x i) * ∏ j ∈ univ.erase i, (X + C (x j))
      = C (Fintype.card ι : ℝ) * ∏ j, (X + C (x j))
        - X * ∑ i, ∏ j ∈ univ.erase i, (X + C (x j)) := by
    rw [← hd, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  calc ∑ i, (X ^ 2 - C (x i)) * ∏ j ∈ univ.erase i, (X + C (x j))
      = X ^ 2 * ∑ i, ∏ j ∈ univ.erase i, (X + C (x j))
        - ∑ i, C (x i) * ∏ j ∈ univ.erase i, (X + C (x j)) := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ = _ := by rw [hx, hP']; ring

theorem Ellipsoid.aux_vieta (x : ι → ℝ) :
    ∏ j, (X + C (x j)) = ∑ k ∈ range (Fintype.card ι + 1),
      C (Ellipsoid.halderElemSymm x k) * X ^ (Fintype.card ι - k) := by -- --- PROOF ---
  have h := Multiset.prod_X_add_C_eq_sum_esymm (univ.val.map x)
  rw [Multiset.map_map] at h
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ] at h
  have hesymm : ∀ k, (univ.val.map x).esymm k = Ellipsoid.halderElemSymm x k :=
    fun k => Finset.esymm_map_val x univ k
  simp only [hesymm] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 24]: (22) is `d β^(d+1) + ∑_{r=1}^{d+1} µᵣ β^(d+1−r)`, with the `µᵣ` of (23). -/
theorem Ellipsoid.halder_poly_expand [DecidableEq ι] (lam : ι → ℝ) (β : ℝ) :
    ∑ i, (β ^ 2 - 1 / lam i) * ∏ j ∈ univ.erase i, (β + 1 / lam j)
      = (Fintype.card ι : ℝ) * β ^ (Fintype.card ι + 1)
        + ∑ r ∈ range (Fintype.card ι + 1), Ellipsoid.halderMu lam (r + 1)
          * β ^ (Fintype.card ι - r) := by -- --- PROOF ---
  set d := Fintype.card ι with hd
  set e : ℕ → ℝ := fun k => Ellipsoid.halderElemSymm (fun i => 1 / lam i) k with he
  have hS := congrArg (eval β) (Ellipsoid.aux_poly_identity (fun i => 1 / lam i))
  simp only [eval_finsetSum, eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_prod, eval_add,
    ← hd] at hS
  have hPeval : ∏ x, (β + 1 / lam x) = ∑ k ∈ range (d + 1), e k * β ^ (d - k) := by
    have := congrArg (eval β) (Ellipsoid.aux_vieta (fun i => 1 / lam i))
    simp only [eval_finsetSum, eval_prod, eval_mul, eval_C, eval_pow, eval_X, eval_add,
      ← hd] at this
    exact this
  rw [hS, Ellipsoid.aux_vieta]
  simp only [← hd]
  -- the polynomial and its derivative, at `β`
  have hP' : eval β (derivative (∑ k ∈ range (d + 1), C (e k) * X ^ (d - k)))
      = ∑ k ∈ range (d + 1), e k * (((d - k : ℕ) : ℝ) * β ^ (d - k - 1)) := by
    simp [eval_finsetSum, derivative_X_pow]
  rw [hP', hPeval]
  -- the edge cases: `e 0 = 1` and `e (d+1) = 0`
  have he0 : e 0 = 1 := by simp [he, Ellipsoid.halderElemSymm]
  have hed : e (d + 1) = 0 := by
    simp only [he, Ellipsoid.halderElemSymm]
    rw [Finset.powersetCard_eq_empty.2 (by simp [hd]), Finset.sum_empty]
  -- termwise: `(β² + β) (d − k) β^(d−k−1) = (d − k)(β^(d−k+1) + β^(d−k))`
  have hterm : ∀ k ∈ range (d + 1), (β ^ 2 + β) * (e k * (((d - k : ℕ) : ℝ) * β ^ (d - k - 1)))
      = ((d : ℝ) - k) * e k * β ^ (d - k + 1) + ((d : ℝ) - k) * e k * β ^ (d - k) := by
    intro k hk
    have hkd : k ≤ d := by simpa [Nat.lt_succ_iff] using hk
    rw [Nat.cast_sub hkd]
    rcases Nat.eq_zero_or_pos (d - k) with h0 | hpos
    · rw [h0]
      have : (d : ℝ) - k = 0 := by
        have := congrArg (Nat.cast (R := ℝ)) h0
        rw [Nat.cast_sub hkd] at this; simpa using this
      rw [this]; simp
    · obtain ⟨m, hm⟩ : ∃ m, d - k = m + 1 := ⟨d - k - 1, by omega⟩
      rw [hm]; simp only [Nat.add_sub_cancel]
      ring
  have hmu : ∀ r : ℕ, Ellipsoid.halderMu lam (r + 1)
      = ((d : ℝ) - (r + 1)) * e (r + 1) - r * e r := by
    intro r
    simp [Ellipsoid.halderMu, he, hd]
  -- the shifted sum: `∑ (d − k) eₖ β^(d−k+1) = d β^(d+1) + ∑ (d − r − 1) e_(r+1) β^(d−r)`
  have key : ∑ k ∈ range (d + 1), ((d : ℝ) - k) * e k * β ^ (d - k + 1)
      = (d : ℝ) * β ^ (d + 1)
        + ∑ r ∈ range (d + 1), ((d : ℝ) - (r + 1)) * e (r + 1) * β ^ (d - r) := by
    rw [sum_range_succ' (fun k => ((d : ℝ) - k) * e k * β ^ (d - k + 1)),
      sum_range_succ (fun r => ((d : ℝ) - (r + 1)) * e (r + 1) * β ^ (d - r))]
    have hlast : ((d : ℝ) - (d + 1)) * e (d + 1) * β ^ (d - d) = 0 := by rw [hed]; simp
    rw [hlast, add_zero, he0]
    have hsum : ∑ k ∈ range d, ((d : ℝ) - ((k + 1 : ℕ) : ℝ)) * e (k + 1) * β ^ (d - (k + 1) + 1)
        = ∑ r ∈ range d, ((d : ℝ) - (r + 1)) * e (r + 1) * β ^ (d - r) := by
      refine sum_congr rfl fun k hk => ?_
      have hk' : k < d := mem_range.1 hk
      rw [show d - (k + 1) + 1 = d - k by omega]
      push_cast
      ring
    rw [hsum]
    simp
    ring
  -- assemble both sides as sums over `range (d + 1)`
  rw [mul_sum, mul_sum]
  calc ∑ k ∈ range (d + 1), (β ^ 2 + β) * (e k * (((d - k : ℕ) : ℝ) * β ^ (d - k - 1)))
        - ∑ k ∈ range (d + 1), (d : ℝ) * (e k * β ^ (d - k))
      = ∑ k ∈ range (d + 1), (((d : ℝ) - k) * e k * β ^ (d - k + 1)
          - k * e k * β ^ (d - k)) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun k hk => ?_
        rw [hterm k hk]
        ring
    _ = (d : ℝ) * β ^ (d + 1)
        + ∑ r ∈ range (d + 1), Ellipsoid.halderMu lam (r + 1) * β ^ (d - r) := by
        rw [sum_sub_distrib, key]
        simp_rw [hmu]
        simp only [sub_mul, sum_sub_distrib]
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
