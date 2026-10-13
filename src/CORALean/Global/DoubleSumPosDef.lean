import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

/-!
# A double sum of matrices weighted by a probability vector is positive definite

The relaxation [1, Lemma 2] quotes, corrected: for `r` vertices, symmetric `Γᵢⱼ` with `Γᵢᵢ ≻ 0`
and `2/(r-1) Γᵢᵢ + Γᵢⱼ + Γⱼᵢ ≻ 0` for every ordered pair `i ≠ j`, the matrix
`Σᵢ Σⱼ μᵢ μⱼ Γᵢⱼ` is positive definite for every `μ ≥ 0` with `Σᵢ μᵢ = 1`. The paper requires the
second condition only for `i < j` and only `≽ 0`, which fails (`doubleSum_posDef_counterexample`).
In the form at `x ≠ 0`, `qᵢⱼ = xᵀΓᵢⱼx`: the two conditions bound `qᵢⱼ + qⱼᵢ` below by
`-2/(r-1) min(qᵢᵢ, qⱼⱼ) ≥ -2/(r-1) √(qᵢᵢ qⱼⱼ)`, so with `aᵢ = μᵢ √qᵢᵢ` twice the form is at least
`(2 + c) Σ aᵢ² - c (Σ aᵢ)²`, `c = 2/(r-1)`, which is nonnegative by Cauchy-Schwarz; strictly
positive since either some pair has `μᵢ μⱼ > 0`, where the bound is strict, or one `μᵢ = 1`.

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ι : Type} [Fintype ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the scalar form of the relaxation
theorem aux_doubleSum_pos {r : ℕ} (q : Fin r → Fin r → ℝ) (μ : Fin r → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) (hd : ∀ i, 0 < q i i)
    (ho : ∀ i j, i ≠ j → 0 < 2 / ((r : ℝ) - 1) * q i i + q i j + q j i) :
    0 < ∑ i, ∑ j, μ i * μ j * q i j := by -- --- PROOF ---
  set c : ℝ := 2 / ((r : ℝ) - 1)
  set a : Fin r → ℝ := fun i => μ i * Real.sqrt (q i i)
  -- `c (r - 1) = 2` once two vertices exist, so `2 + c - c r ≥ 0` always
  have hc : 0 ≤ c ∧ 0 ≤ 2 + c - c * r := by
    have hr : (1 : ℝ) ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp at hμ1
      · exact_mod_cast h0
    have hc0 : 0 ≤ c := div_nonneg (by norm_num) (by linarith)
    refine ⟨hc0, ?_⟩
    -- `c (r - 1)` is `2`, or `0` at one vertex
    have hcr : c * ((r : ℝ) - 1) ≤ 2 := by
      rcases (sub_nonneg.mpr hr).lt_or_eq with h | h
      · simp only [c]; rw [div_mul_cancel₀ _ h.ne']
      · rw [← h, mul_zero]; norm_num
    nlinarith
  -- off the diagonal, `qᵢⱼ + qⱼᵢ > -c √qᵢᵢ √qⱼⱼ`
  have hoff : ∀ i j, i ≠ j →
      -c * (Real.sqrt (q i i) * Real.sqrt (q j j)) < q i j + q j i := fun i j hij => by
    have h1 := ho i j hij
    have h2 := ho j i hij.symm
    have hsi := Real.sq_sqrt (hd i).le
    have hsj := Real.sq_sqrt (hd j).le
    have hs0i := Real.sqrt_nonneg (q i i)
    have hs0j := Real.sqrt_nonneg (q j j)
    -- `min(qᵢᵢ, qⱼⱼ) ≤ √qᵢᵢ √qⱼⱼ`
    rcases le_total (Real.sqrt (q i i)) (Real.sqrt (q j j)) with hle | hle
    · have : q i i ≤ Real.sqrt (q i i) * Real.sqrt (q j j) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hc.1]
    · have : q j j ≤ Real.sqrt (q i i) * Real.sqrt (q j j) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hc.1]
  -- the pairwise bound `L i j`, `2aᵢ²` on the diagonal and `-c aᵢ aⱼ` off it
  set L : Fin r → Fin r → ℝ := fun i j => -c * (a i * a j) + if i = j then (2 + c) * a i ^ 2 else 0
  have hmu : ∀ i j, a i * a j = μ i * μ j * (Real.sqrt (q i i) * Real.sqrt (q j j)) :=
    fun i j => by simp only [a]; ring
  have hkey : ∀ i j, i ≠ j → 0 < μ i * μ j → L i j < μ i * μ j * (q i j + q j i) :=
    fun i j hij hp => by
      simp only [L, if_neg hij, add_zero, hmu]
      have := mul_lt_mul_of_pos_left (hoff i j hij) hp
      linarith
  -- and the bound holds everywhere, with equality on the diagonal
  have hkey' : ∀ i j, L i j ≤ μ i * μ j * (q i j + q j i) := fun i j => by
    by_cases hij : i = j
    · subst hij
      have ha2 : a i ^ 2 = μ i ^ 2 * q i i := by
        simp only [a, mul_pow, Real.sq_sqrt (hd i).le]
      simp only [L, if_true, sq] at ha2 ⊢
      nlinarith [ha2]
    · rcases (mul_nonneg (hμ0 i) (hμ0 j)).lt_or_eq with hp | hp
      · exact (hkey i j hij hp).le
      · simp only [L, if_neg hij, add_zero, hmu, ← hp]; simp
  -- twice the form is the symmetrized double sum
  have htwice : 2 * ∑ i, ∑ j, μ i * μ j * q i j = ∑ i, ∑ j, μ i * μ j * (q i j + q j i) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => μ i * μ j * q j i)]
    simp only [mul_comm (μ _) (μ _)]
    ring
  -- `Σ L = (2 + c) Σ aᵢ² - c (Σ aᵢ)² ≥ 0` by Cauchy-Schwarz
  have hL : 0 ≤ ∑ i, ∑ j, L i j := by
    have hsum : ∑ i, ∑ j, L i j = (2 + c) * ∑ i, a i ^ 2 - c * (∑ i, a i) ^ 2 := by
      simp only [L, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, sq, Finset.sum_mul_sum]
      ring
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    have hsq : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left hcs hc.1, mul_nonneg hc.2 hsq]
  by_cases hpair : ∃ i j, i ≠ j ∧ 0 < μ i * μ j
  · -- a pair with weight on both: the bound is strict there
    obtain ⟨i₀, j₀, hij, hp⟩ := hpair
    have hlt : ∑ i, ∑ j, L i j < ∑ i, ∑ j, μ i * μ j * (q i j + q j i) := by
      refine Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => hkey' i j)
        ⟨i₀, Finset.mem_univ _, Finset.sum_lt_sum (fun j _ => hkey' i₀ j)
          ⟨j₀, Finset.mem_univ _, hkey i₀ j₀ hij hp⟩⟩
    linarith
  · -- otherwise the weight sits on one vertex, and the form is `μᵢ² qᵢᵢ` summed
    push Not at hpair
    have hz : ∀ i j, i ≠ j → μ i * μ j = 0 := fun i j hij =>
      le_antisymm (hpair i j hij) (mul_nonneg (hμ0 i) (hμ0 j))
    have hdiag : ∑ i, ∑ j, μ i * μ j * q i j = ∑ i, μ i * μ i * q i i := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
      rw [hz i j (Ne.symm hj), zero_mul]
    obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ Finset.univ, 0 < μ i := by
      by_contra hc
      push Not at hc
      have : ∑ i, μ i ≤ 0 := Finset.sum_nonpos fun i hi => hc i hi
      linarith
    rw [hdiag]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (mul_nonneg (hμ0 i) (hμ0 i)) (hd i).le)
      ⟨i₀, Finset.mem_univ _, mul_pos (mul_pos hi₀ hi₀) (hd i₀)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem doubleSum_posDef {r : ℕ} (Γ : Fin r → Fin r → Matrix ι ι ℝ) (μ : Fin r → ℝ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) (hsym : ∀ i j, (Γ i j)ᵀ = Γ i j)
    (hd : ∀ i, (Γ i i).PosDef)
    (ho : ∀ i j, i ≠ j → ((2 / ((r : ℝ) - 1)) • Γ i i + Γ i j + Γ j i).PosDef) :
    (∑ i, ∑ j, (μ i * μ j) • Γ i j).PosDef := by -- --- PROOF ---
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · -- symmetric, every `Γᵢⱼ` being
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp only [transpose_sum, transpose_smul, hsym]
  -- the scalar relaxation at the forms `qᵢⱼ = xᵀΓᵢⱼx`
  have hq : ∀ (M : Matrix ι ι ℝ), M.PosDef → 0 < x ⬝ᵥ (M *ᵥ x) := fun M hM => by
    simpa using (posDef_iff_dotProduct_mulVec.mp hM).2 hx
  have h := aux_doubleSum_pos (fun i j => x ⬝ᵥ (Γ i j *ᵥ x)) μ hμ0 hμ1 (fun i => hq _ (hd i))
    (fun i j hij => by
      have := hq _ (ho i j hij)
      simpa only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
        using this)
  rw [star_trivial]
  simpa only [sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
