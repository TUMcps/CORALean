module

public import CORALean.ContDynamics.LinearARX.Operations.OfCharpoly

@[expose] public section

/-!
# The state-space outputs satisfy the ARMAX recursion, by Cayley-Hamilton

Every run of `x(k+1) = A x(k) + B̃ ũ(k)`, `y(k) = C x(k) + D̃ ũ(k)` satisfies the recursion of
`ofCharpoly` from `k = n` on [1]: unroll `x(k-j)` from `x(k-n)`, and `∑ a_j A^{n-j} = 0`
removes `x(k-n)`; what is left is the convolution of `a` with the impulse response.

## Inputs
* `A` – state matrix
* `Bu` – input matrix
* `C` – output matrix
* `Du` – feedthrough matrix
* `dt` – sampling time
* `x` – states
* `u` – inputs
* `y` – outputs
* `k` – step

## Hypotheses
* `hx` – state recursion holds
* `hy` – output equation holds
* `hk` – step at least the order

## Conclusion
* the output satisfies the ARMAX recursion

## References

* [1] `contDynamics/@linearSysDT/linearARX.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n dy du : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state `q` steps on: the free response and the inputs in between. -/
theorem aux_charpoly_unroll (A : Mat ℝ n n) (Bu : Mat ℝ n du) {x : ℕ → Vec ℝ n}
    {u : ℕ → Vec ℝ du} (hx : ∀ k, x (k + 1) = A *ᵥ x k + Bu *ᵥ u k) (t : ℕ) : -- --- CONCL ---
    ∀ q, x (t + q) = A ^ q *ᵥ x t
      + ∑ m ∈ Finset.range q, (A ^ (q - 1 - m) * Bu) *ᵥ u (t + m) := by -- --- PROOF ---
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, hx, ih, Finset.sum_range_succ, mulVec_add, mulVec_sum, mulVec_mulVec,
      ← pow_succ']
    have hsum : ∑ m ∈ Finset.range q, A *ᵥ ((A ^ (q - 1 - m) * Bu) *ᵥ u (t + m))
        = ∑ m ∈ Finset.range q, (A ^ (q + 1 - 1 - m) * Bu) *ᵥ u (t + m) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.mp hm
      rw [mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
      congr 3
      omega
    rw [hsum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mul]
    abel

/-- The two triangular sums of the proof, one by the lag `j` and the step `m` after `k - n`, the
other by the lag `s = n - m` of the input and the coefficient `i = j`. -/
theorem aux_charpoly_triangle {α : Type} [AddCommMonoid α] (n : ℕ)
    (F : ℕ → ℕ → ℕ → α) : -- --- CONCL ---
    ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n - j), F j m (n - j - 1 - m)
      = ∑ s ∈ Finset.range (n + 1), ∑ i ∈ Finset.range s,
        F i (n - s) (s - i - 1) := by -- --- PROOF ---
  -- both double sums over sigma types, matched by `(j, m) ↦ (n - m, j)`
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨n - p.2, p.1⟩) (fun p _ => ⟨p.2, n - p.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    ext
    · simp
    · simp; omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    ext
    · simp; omega
    · simp
  · -- the summands agree: `n - (n - m) = m` and the exponents are one number
    intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have h1 : n - (n - p.2) = p.2 := by omega
    have h2 : n - p.2 - p.1 - 1 = n - p.1 - 1 - p.2 := by omega
    simp only [h1, h2]

/-- Cayley-Hamilton in the order `a_j A^{n-j}`. -/
theorem aux_charpoly_cayleyHamilton (A : Mat ℝ n n) : -- --- CONCL ---
    ∑ j ∈ Finset.range (n + 1), A.charpoly.coeff (n - j) • A ^ (n - j) = 0 := by -- --- PROOF ---
  have h := Matrix.aeval_self_charpoly A
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim] at h
  simp only [Fintype.card_fin] at h
  rw [← h, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [Nat.add_sub_cancel, show n - (n - j) = j by omega]

/-- The convolution of the coefficients with the outputs is that of the impulse response with the
inputs. -/
theorem aux_charpoly_convolution (A : Mat ℝ n n) (Bu : Mat ℝ n du) (C : Mat ℝ dy n)
    (Du : Mat ℝ dy du) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ du} {y : ℕ → Vec ℝ dy}
    (hx : ∀ k, x (k + 1) = A *ᵥ x k + Bu *ᵥ u k) (hy : ∀ k, y k = C *ᵥ x k + Du *ᵥ u k)
    (t : ℕ) : -- --- CONCL ---
    ∑ j ∈ Finset.range (n + 1), A.charpoly.coeff (n - j) • y (n + t - j)
      = ∑ s ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (s + 1), A.charpoly.coeff (n - i) •
        (if s - i = 0 then Du else C * A ^ (s - i - 1) * Bu)) *ᵥ
        u (n + t - s) := by -- --- PROOF ---
  set a : ℕ → ℝ := fun j => A.charpoly.coeff (n - j) with ha
  -- each output, from `x t`: the free response, the inputs in between, the feedthrough
  have hyj : ∀ j ∈ Finset.range (n + 1), a j • y (n + t - j)
      = a j • (C *ᵥ (A ^ (n - j) *ᵥ x t))
        + ∑ m ∈ Finset.range (n - j), a j • ((C * (A ^ (n - j - 1 - m) * Bu)) *ᵥ u (t + m))
        + a j • (Du *ᵥ u (n + t - j)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [hy, show n + t - j = t + (n - j) by omega, aux_charpoly_unroll A Bu hx t (n - j),
      mulVec_add, mulVec_sum]
    simp only [mulVec_mulVec, smul_add, Finset.smul_sum]
  rw [Finset.sum_congr rfl hyj, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the free response is gone by Cayley-Hamilton
  have hfree : ∑ j ∈ Finset.range (n + 1), a j • (C *ᵥ (A ^ (n - j) *ᵥ x t)) = 0 := by
    have hch := congrArg (fun M => C *ᵥ (M *ᵥ x t)) (aux_charpoly_cayleyHamilton A)
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, mulVec_sum, mulVec_smul, zero_mulVec,
      mulVec_zero] at hch
    exact hch
  rw [hfree, zero_add]
  -- the right side: the feedthrough term is the last of each inner sum
  have hrhs : ∀ s ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (s + 1), a i •
      (if s - i = 0 then Du else C * A ^ (s - i - 1) * Bu)) *ᵥ u (n + t - s)
      = a s • (Du *ᵥ u (n + t - s)) + ∑ i ∈ Finset.range s,
        a i • ((C * A ^ (s - i - 1) * Bu) *ᵥ u (n + t - s)) := by
    intro s _
    rw [Finset.sum_range_succ, Matrix.add_mulVec, Matrix.sum_mulVec]
    simp only [Nat.sub_self, if_true, Matrix.smul_mulVec]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
  rw [Finset.sum_congr rfl hrhs, Finset.sum_add_distrib, add_comm]
  congr 1
  -- the two triangular sums are one
  have htri := aux_charpoly_triangle n (fun j m e => a j • ((C * A ^ e * Bu) *ᵥ u (t + m)))
  simp only [Matrix.mul_assoc] at htri ⊢
  refine htri.trans (Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun i _ => ?_)
  rw [show n + t - s = t + (n - s) by have := Finset.mem_range.mp hs; omega]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.ofCharpoly_step (A : Mat ℝ n n) (Bu : Mat ℝ n du) (C : Mat ℝ dy n)
    (Du : Mat ℝ dy du) (dt : ℝ) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ du} {y : ℕ → Vec ℝ dy}
    (hx : ∀ k, x (k + 1) = A *ᵥ x k + Bu *ᵥ u k) (hy : ∀ k, y k = C *ᵥ x k + Du *ᵥ u k)
    (k : ℕ) (hk : n ≤ k) : -- --- CONCL ---
    y k = ∑ i : Fin n, toRealMat ((LinearARX.ofCharpoly A Bu C Du dt).Abar i) *ᵥ y (k - (i + 1))
      + ∑ j : Fin (n + 1),
        toRealMat ((LinearARX.ofCharpoly A Bu C Du dt).Bbar j) *ᵥ u (k - j) := by -- --- PROOF ---
  -- the identity of `aux_charpoly_convolution`, with `a₀ = 1` split off the left side
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hK := aux_charpoly_convolution A Bu C Du hx hy t
  have ha0 : A.charpoly.coeff (n - 0) = 1 := by
    have := (Matrix.charpoly_monic A).coeff_natDegree
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [Finset.sum_range_succ', ha0, one_smul] at hK
  simp only [Nat.sub_zero] at hK
  -- `Ā_i y = -a_i y`, the scaled identity acting on a vector
  have hA : ∀ (c : ℝ) (v : Vec ℝ dy), (-c • (1 : Mat ℝ dy dy)) *ᵥ v = -(c • v) := by
    intro c v
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, neg_smul]
  simp only [LinearARX.ofCharpoly, Scalar.toRealMat_real, hA, Finset.sum_neg_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun i => (A.charpoly.coeff (n - (i + 1))) • y (n + t - (i + 1))) n,
    Fin.sum_univ_eq_sum_range (fun j => (∑ i ∈ Finset.range (j + 1), A.charpoly.coeff (n - i) •
      (if j - i = 0 then Du else C * A ^ (j - i - 1) * Bu)) *ᵥ u (n + t - j)) (n + 1)]
  rw [← hK]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
