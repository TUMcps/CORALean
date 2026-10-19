module

public import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmi

@[expose] public section

/-!
# The `H₋` inequality makes the residual fault-sensitive

[1, Eq. 21], [1, Eq. 24]: with no disturbance or noise, the error `e_k = x_k - p_k` follows
`e_{k+1} = (A - LC) e_k - L E f_k` [1, Eq. 19] and the residual center is
`r_k = M C e_k + M E f_k` [1, Eq. 20]. If `P ≻ 0`, `α ≥ 0`, `W` and `β` satisfy [1, Eq. 27]
(`LinearSysDT.HMinusLmi`) with `Y = MᵀM`, then at `L = P⁻¹W`, from `e_0 = 0`, every fault sequence
with `f_{k₀} ≠ 0` has `J^N_- = Σ_{k<N} (r_kᵀr_k - β² f_kᵀf_k) ≥ c > 0` [1, Eq. 21] for all `N > k₀`,
`c` independent of `N`: the `H₋` performance `‖r‖²₂ > β²‖f‖²₂` over every horizon, and in the limit.

The chain of the paper, run backwards. At `(w, e, f)` with `w = e_{k+1}` the form of the negated
Eq. 27 is `r_kᵀr_k - β²f_kᵀf_k - ΔV_k` with `V_k = e_kᵀ(αP)e_k` [1, Eq. 22], `Q = αP` (the
substitution of [1, Eq. 26] into Eq. 27): the first block row of Eq. 26 is `Q(A - LC)` and `-QLE`
once `W = PL`, so the cross terms give `2 wᵀQw`. That is [1, Eq. 24] (and [1, Eq. 25], its form
in `(e, f)`), positive whenever `f_k ≠ 0`, nonnegative always. Summing and telescoping,
`J^N_- = Σ_k (r_kᵀr_k - β²f_kᵀf_k - ΔV_k) + V_N` with `V_0 = 0` [1, Eq. 23], and `V_N ≥ 0`.

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- [1, Eq. 24] at one step: the form of the negated Eq. 27 at `(e_{k+1}, e_k, f_k)`
theorem LinearSysDT.aux_hMinus_step (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf)
    (P : Mat ℝ n n) (W : Mat ℝ n ny) (M : Mat ℝ ny ny) (α β : ℝ) (hP : P.PosDef)
    (h : LinearSysDT.HMinusLmi A C E P W (Mᵀ * M) α β) (e : Vec ℝ n)
    (f : Vec ℝ nf) : -- --- CONCL ---
    let L := P⁻¹ * W
    let w := (A - L * C) *ᵥ e - (L * E) *ᵥ f
    let r := (M * C) *ᵥ e + (M * E) *ᵥ f
    let term := r ⬝ᵥ r - β ^ 2 * (f ⬝ᵥ f) - (w ⬝ᵥ ((α • P) *ᵥ w) - e ⬝ᵥ ((α • P) *ᵥ e))
    0 ≤ term ∧ (f ≠ 0 → 0 < term) := by -- --- PROOF ---
  intro L w r term
  haveI : Invertible P := hP.isUnit.invertible
  set Q := α • P with hQ
  set R : Matrix (Fin n) (Fin n ⊕ Fin nf) ℝ :=
    fromCols (α • (P * A) - α • (W * C)) (-(α • (W * E))) with hR
  set D : Matrix (Fin n ⊕ Fin nf) (Fin n ⊕ Fin nf) ℝ :=
    fromBlocks (-(α • P) - Cᵀ * (Mᵀ * M) * C) (-(Cᵀ * (Mᵀ * M) * E)) (-(Cᵀ * (Mᵀ * M) * E))ᵀ
      (-(Eᵀ * (Mᵀ * M) * E) + β ^ 2 • 1) with hD
  have hPL : P * L = W := by
    simp only [L, ← Matrix.mul_assoc, mul_inv_of_invertible, Matrix.one_mul]
  -- `R (e, f) = Q w`
  have hRv : R *ᵥ Sum.elim e f = Q *ᵥ w := by
    simp only [hR, hQ, w, fromCols_mulVec_sumElim, sub_mulVec, smul_mulVec, neg_mulVec,
      mulVec_sub, ← mulVec_mulVec, ← hPL]
    simp only [mulVec_mulVec, ← Matrix.mul_assoc]
    abel_nf
  -- `Xᵀ MᵀM Z` as a dot product of `M X` and `M Z`
  have hY : ∀ {k l : ℕ} (X : Mat ℝ ny k) (Z : Mat ℝ ny l) (a : Vec ℝ k) (b : Vec ℝ l),
      a ⬝ᵥ ((Xᵀ * (Mᵀ * M) * Z) *ᵥ b) = ((M * X) *ᵥ a) ⬝ᵥ ((M * Z) *ᵥ b) := by
    intro k l X Z a b
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, mulVec_mulVec]
  have hDv : Sum.elim e f ⬝ᵥ ((-D) *ᵥ Sum.elim e f) =
      e ⬝ᵥ (Q *ᵥ e) + r ⬝ᵥ r - β ^ 2 * (f ⬝ᵥ f) := by
    have hT : f ⬝ᵥ ((-(Cᵀ * (Mᵀ * M) * E))ᵀ *ᵥ e) = -(e ⬝ᵥ ((Cᵀ * (Mᵀ * M) * E) *ᵥ f)) := by
      rw [transpose_neg, neg_mulVec, dotProduct_neg, mulVec_transpose, dotProduct_comm,
        ← dotProduct_mulVec]
    simp only [hD, neg_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_add, add_mulVec, sub_mulVec,
      neg_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, one_mulVec, smul_eq_mul]
    rw [hT, hY C C, hY C E, hY E E]
    simp only [r, hQ, add_dotProduct, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm ((M * E) *ᵥ f) ((M * C) *ᵥ e)]
    ring
  -- the whole form at `(w, e, f)` is the term
  set v : (Fin n ⊕ (Fin n ⊕ Fin nf)) → ℝ := Sum.elim w (Sum.elim e f)
  have hform : v ⬝ᵥ ((-(fromBlocks (-(α • P)) R Rᵀ D)) *ᵥ v) = term := by
    have hRT : Sum.elim e f ⬝ᵥ ((-Rᵀ) *ᵥ w) = -(w ⬝ᵥ (Q *ᵥ w)) := by
      rw [neg_mulVec, dotProduct_neg, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, hRv]
    have h1 : Sum.elim e f ⬝ᵥ (Rᵀ *ᵥ w) = w ⬝ᵥ (Q *ᵥ w) := by
      rw [neg_mulVec, dotProduct_neg] at hRT; linarith
    have h2 : Sum.elim e f ⬝ᵥ (D *ᵥ Sum.elim e f) =
        -(e ⬝ᵥ (Q *ᵥ e) + r ⬝ᵥ r - β ^ 2 * (f ⬝ᵥ f)) := by
      rw [neg_mulVec, dotProduct_neg] at hDv; linarith
    simp only [v, fromBlocks_neg, neg_neg, fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, sumElim_dotProduct_sumElim, dotProduct_add, neg_mulVec,
      dotProduct_neg, hRv]
    rw [h1, h2]
    simp only [term, hQ]
    ring
  -- positive definite: nonnegative everywhere, positive off `0`
  have hq := (posDef_iff_dotProduct_mulVec.mp h).2
  refine ⟨?_, fun hf => ?_⟩
  · by_cases hv : v = 0
    · rw [← hform, hv]; simp
    · rw [← hform]; exact (hq hv).le
  · have hv : v ≠ 0 := fun h0 => hf (funext fun i => by
      simpa [v] using congrFun h0 (Sum.inr (Sum.inr i)))
    rw [← hform]; exact hq hv


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.hMinus_of_lmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf) (P : Mat ℝ n n)
    (W : Mat ℝ n ny) (M : Mat ℝ ny ny) (α β : ℝ) (hP : P.PosDef) (hα : 0 ≤ α)
    (h : LinearSysDT.HMinusLmi A C E P W (Mᵀ * M) α β) (e : ℕ → Vec ℝ n) (f : ℕ → Vec ℝ nf)
    (he0 : e 0 = 0)
    (he : ∀ k, e (k + 1) = (A - P⁻¹ * W * C) *ᵥ e k - (P⁻¹ * W * E) *ᵥ f k)
    (k₀ : ℕ) (hf : f k₀ ≠ 0) : -- --- CONCL ---
    let r : ℕ → Vec ℝ ny := fun k => (M * C) *ᵥ e k + (M * E) *ᵥ f k        -- Eq. 20
    ∃ c > 0, ∀ N, k₀ < N →
      c ≤ ∑ k ∈ Finset.range N, (r k ⬝ᵥ r k - β ^ 2 * (f k ⬝ᵥ f k)) := by -- --- PROOF ---
  intro r
  set V : ℕ → ℝ := fun k => e k ⬝ᵥ ((α • P) *ᵥ e k) with hV
  set T : ℕ → ℝ := fun k => r k ⬝ᵥ r k - β ^ 2 * (f k ⬝ᵥ f k) - (V (k + 1) - V k) with hT
  have hstep : ∀ k, 0 ≤ T k ∧ (f k ≠ 0 → 0 < T k) := by
    intro k
    have := LinearSysDT.aux_hMinus_step A C E P W M α β hP h (e k) (f k)
    simp only [hT, hV, he k]
    exact this
  refine ⟨T k₀, (hstep k₀).2 hf, fun N hN => ?_⟩
  -- the sum is the terms plus the telescoped `V_N - V_0`, `V_0 = 0`, `V_N ≥ 0`
  have hsplit : ∑ k ∈ Finset.range N, (r k ⬝ᵥ r k - β ^ 2 * (f k ⬝ᵥ f k)) =
      ∑ k ∈ Finset.range N, T k + (V N - V 0) := by
    rw [← Finset.sum_range_sub V N, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hT]; ring
  have hV0 : V 0 = 0 := by simp [hV, he0]
  have hVN : 0 ≤ V N := by
    simp only [hV, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hα (hP.posSemidef.dotProduct_mulVec_nonneg (e N) |>.trans_eq (by simp))
  have hle : T k₀ ≤ ∑ k ∈ Finset.range N, T k :=
    Finset.single_le_sum (fun k _ => (hstep k).1) (Finset.mem_range.mpr hN)
  rw [hsplit, hV0]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
