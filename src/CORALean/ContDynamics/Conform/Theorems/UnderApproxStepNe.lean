import CORALean.Global.Tensor
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# [1, Eq. 7] is not an equality for [1, Eq. 2]'s inner approximation

[1, Eq. 2] keeps the disturbance constant over the whole of `[0, t]`, so that
`R_x(t) - x̃(t) = e^{At} X̃₀ ⊕ Υ(t) W_c`, `Υ(t) w = ∫₀ᵗ e^{A(t-τ)} w dτ`. [1, Eq. 7] states
`R_x(t_{k+1}) - x̃(t_{k+1}) = e^{Ah}(R_x(t_k) - x̃(t_k)) ⊕ Υ(h) W_c`. The right side lets the
disturbance change at `t_k`; the left does not. As `Υ(t_{k+1}) = e^{Ah} Υ(t_k) + Υ(h)`, the left is
`{(e^{Ah} Υ(t_k) + Υ(h)) w}` and the right `e^{Ah} Υ(t_k) W_c ⊕ Υ(h) W_c`, a strictly larger set
once the two images point different ways: at `A = [0 1; 0 0]`, `h = 1`, `k = 1`, `X̃₀ = {0}`,
`W_c = {0} × [-1, 1]`, the left is the segment `{s (2, 2)}` and the right a parallelogram
containing `(1, 0)`. The right side, iterated, is the reachable set under disturbances
constant on each step, which is what [1, Eq. 8] and the discrete-time model use; it lies
between [1, Eq. 2]'s inner approximation and the exact reachable set, so conformance
established against it is still conformance of the continuous model.

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The nilpotent `A = [0 1; 0 0]`: `e^{sA} = I + s A`. -/
theorem aux_exp_nil (s : ℝ) :
    exp (s • !![(0 : ℝ), 1; 0, 0]) = 1 + s • !![(0 : ℝ), 1; 0, 0] := by -- --- PROOF ---
  have hA2 : !![(0 : ℝ), 1; 0, 0] ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hpow : ∀ m, 2 ≤ m → (s • !![(0 : ℝ), 1; 0, 0]) ^ m = 0 := fun m hm => by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, smul_pow, hA2, smul_zero, zero_mul]
  rw [exp_eq_tsum ℝ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 2) fun m hm => by
    rw [hpow m (by simp only [Finset.mem_range, not_lt] at hm; omega), smul_zero]]
  simp [Finset.sum_range_succ]

/-- `A (a, b) = (b, 0)`. -/
theorem aux_nil_mulVec (a b : ℝ) : !![(0 : ℝ), 1; 0, 0] *ᵥ ![a, b] = ![b, 0] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `Υ(t) w = t w + (t²/2) A w` for the nilpotent `A`. -/
theorem aux_upsilon (t : ℝ) (w : Vec ℝ 2) :
    ∫ τ in (0 : ℝ)..t, exp ((t - τ) • !![(0 : ℝ), 1; 0, 0]) *ᵥ w
      = t • w + (t ^ 2 / 2) • (!![(0 : ℝ), 1; 0, 0] *ᵥ w) := by -- --- PROOF ---
  have hint : ∀ τ : ℝ, exp ((t - τ) • !![(0 : ℝ), 1; 0, 0]) *ᵥ w
      = w + (t - τ) • (!![(0 : ℝ), 1; 0, 0] *ᵥ w) := fun τ => by
    rw [aux_exp_nil, add_mulVec, one_mulVec, smul_mulVec]
  simp only [hint]
  have hc : Continuous fun τ : ℝ => (t - τ) • (!![(0 : ℝ), 1; 0, 0] *ᵥ w) :=
    (continuous_const.sub continuous_id).smul continuous_const
  have hlin : ∫ x in (0 : ℝ)..t, (t - x) = t ^ 2 / 2 := by
    have hid : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 t :=
      continuous_id.intervalIntegrable 0 t
    rw [intervalIntegral.integral_sub intervalIntegrable_const hid,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable 0 t),
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const, hlin, sub_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7] fails for [1, Eq. 2]'s sets at `A = [0 1; 0 0]`, `h = 1`, `k = 1`. -/
theorem Conform.underApprox_step_ne :
    ∃ (A : Mat ℝ 2 2) (h : ℝ) (Wc : Set (Vec ℝ 2)), 0 < h ∧
      (fun w => ∫ τ in (0 : ℝ)..(2 * h), exp ((2 * h - τ) • A) *ᵥ w) '' Wc ≠
        (fun x => exp (h • A) *ᵥ x) '' ((fun w => ∫ τ in (0 : ℝ)..h, exp ((h - τ) • A) *ᵥ w) '' Wc)
          + (fun w => ∫ τ in (0 : ℝ)..h, exp ((h - τ) • A) *ᵥ w) '' Wc := by -- --- PROOF ---
  refine ⟨!![0, 1; 0, 0], 1, {w | ∃ s ∈ Set.Icc (-1 : ℝ) 1, w = ![0, s]}, one_pos, fun h => ?_⟩
  simp only [aux_upsilon] at h
  simp only [aux_exp_nil] at h
  -- `(1, 0) = e^A Υ(1) (0, 1) + Υ(1) (0, -1)` is on the right
  have hmem : (![1, 0] : Vec ℝ 2) ∈ (fun x => (1 + (1 : ℝ) • !![(0 : ℝ), 1; 0, 0]) *ᵥ x) ''
      ((fun w => (1 : ℝ) • w + ((1 : ℝ) ^ 2 / 2) • (!![(0 : ℝ), 1; 0, 0] *ᵥ w)) ''
        {w | ∃ s ∈ Set.Icc (-1 : ℝ) 1, w = ![0, s]})
      + (fun w => (1 : ℝ) • w + ((1 : ℝ) ^ 2 / 2) • (!![(0 : ℝ), 1; 0, 0] *ᵥ w)) ''
        {w | ∃ s ∈ Set.Icc (-1 : ℝ) 1, w = ![0, s]} := by
    refine ⟨_, ⟨_, ⟨![0, 1], ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩, rfl⟩, rfl⟩,
      _, ⟨![0, -1], ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩, rfl⟩, ?_⟩
    simp only [aux_nil_mulVec, add_mulVec, one_mulVec, smul_mulVec, Matrix.smul_cons,
      Matrix.cons_add_cons, smul_eq_mul, Matrix.smul_empty, Matrix.empty_add_empty]
    funext i
    fin_cases i <;> simp
  rw [← h] at hmem
  -- the left is `{s (2, 2)}`, which misses `(1, 0)`
  obtain ⟨_, ⟨s, -, rfl⟩, hs⟩ := hmem
  simp only [aux_nil_mulVec, Matrix.smul_cons, Matrix.cons_add_cons, smul_eq_mul,
    Matrix.smul_empty, Matrix.empty_add_empty] at hs
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  simp at h0 h1
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
