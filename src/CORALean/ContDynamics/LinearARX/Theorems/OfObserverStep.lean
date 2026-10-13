import CORALean.ContDynamics.LinearARX.Operations.OfObserver

/-!
# The state-space outputs satisfy the ARMAX recursion

[1, Prop. 2]: every run of `x(k+1) = A x(k) + B̃ ũ(k)`, `y(k) = C x(k) + D̃ ũ(k)` satisfies
the recursion of `ofObserver` from `k = p` on, once `(A + MC)^p = 0`. [1] cites the proof
(Phan et al. 1993); here it is the observer form `x(k+1) = F x(k) + (B̃ + MD̃) ũ(k) - M y(k)`,
`F = A + MC`, unrolled `p` times, `F^p x(k-p)` vanishing.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n dy du : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state after `m` observer steps back from `k`. -/
theorem LinearARX.aux_observer_unroll (A : Mat ℝ n n) (Bu : Mat ℝ n du) (C : Mat ℝ dy n)
    (Du : Mat ℝ dy du) (M : Mat ℝ n dy) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ du}
    {y : ℕ → Vec ℝ dy} (hx : ∀ k, x (k + 1) = A *ᵥ x k + Bu *ᵥ u k)
    (hy : ∀ k, y k = C *ᵥ x k + Du *ᵥ u k) (k : ℕ) :
    ∀ m ≤ k, x k = (A + M * C) ^ m *ᵥ x (k - m) + ∑ i ∈ Finset.range m,
      (A + M * C) ^ i *ᵥ ((Bu + M * Du) *ᵥ u (k - 1 - i)
        - M *ᵥ y (k - 1 - i)) := by -- --- PROOF ---
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    -- one observer step: `x(j+1) = F x(j) + (B̃ + MD̃) ũ(j) - M y(j)`
    have hstep : x (k - m) = (A + M * C) *ᵥ x (k - (m + 1))
        + ((Bu + M * Du) *ᵥ u (k - 1 - m) - M *ᵥ y (k - 1 - m)) := by
      rw [show k - m = (k - (m + 1)) + 1 by omega, hx, show k - 1 - m = k - (m + 1) by omega,
        hy, add_mulVec, add_mulVec, mulVec_add, ← mulVec_mulVec,
        ← mulVec_mulVec (u (k - (m + 1))) M Du]
      abel
    rw [ih (by omega), Finset.sum_range_succ, hstep, mulVec_add, mulVec_mulVec, ← pow_succ]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.ofObserver_step {p : ℕ} (A : Mat ℝ n n) (Bu : Mat ℝ n du) (C : Mat ℝ dy n)
    (Du : Mat ℝ dy du) (M : Mat ℝ n dy) (hM : (A + M * C) ^ p = 0) {x : ℕ → Vec ℝ n}
    {u : ℕ → Vec ℝ du} {y : ℕ → Vec ℝ dy} (hx : ∀ k, x (k + 1) = A *ᵥ x k + Bu *ᵥ u k)
    (hy : ∀ k, y k = C *ᵥ x k + Du *ᵥ u k) (k : ℕ) (hk : p ≤ k) :
    y k = ∑ i : Fin p, toRealMat ((LinearARX.ofObserver p A Bu C Du M).Abar i)
        *ᵥ y (k - (i + 1))
      + ∑ j : Fin (p + 1), toRealMat ((LinearARX.ofObserver p A Bu C Du M).Bbar j)
        *ᵥ u (k - j) := by -- --- PROOF ---
  conv_lhs => rw [hy, LinearARX.aux_observer_unroll A Bu C Du M hx hy k p hk, hM, zero_mulVec,
    zero_add, mulVec_sum]
  simp only [LinearARX.ofObserver, Scalar.toRealMat_real]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, if_true, Nat.sub_zero, Fin.val_succ, Nat.add_one_ne_zero, if_false,
    Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i => -(C * (A + M * C) ^ i * M) *ᵥ y (k - (i + 1))) p,
    Fin.sum_univ_eq_sum_range (fun i => (C * (A + M * C) ^ i * (Bu + M * Du)) *ᵥ
      u (k - (i + 1))) p]
  have hterm : ∀ i ∈ Finset.range p, C *ᵥ ((A + M * C) ^ i *ᵥ ((Bu + M * Du) *ᵥ u (k - 1 - i)
      - M *ᵥ y (k - 1 - i))) = -(C * (A + M * C) ^ i * M) *ᵥ y (k - (i + 1))
        + (C * (A + M * C) ^ i * (Bu + M * Du)) *ᵥ u (k - (i + 1)) := by
    intro i _
    rw [show k - 1 - i = k - (i + 1) by omega, mulVec_sub, mulVec_sub, neg_mulVec,
      mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_assoc]
    abel
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
