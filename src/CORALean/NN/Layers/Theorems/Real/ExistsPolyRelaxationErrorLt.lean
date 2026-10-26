module

public import CORALean.NN.Layers.Definitions.PolyOfSampling
public import CORALean.NN.Layers.Theorems.Real.AbsSubEvalPolyDerivLe
public import CORALean.NN.Layers.Theorems.Real.ExistsEvalPolyNear
public import CORALean.NN.Layers.Theorems.Real.OfSamplingSound
public import CORALean.NN.Layers.Theorems.Real.SampleGridMemIcc

@[expose] public section

/-!
# One relaxation small on every box in a range

ℝ-only, the sampling being exact. A layer has one order and `n` neurons, each with a box of its
own, so what a refinement level [1] must buy is a *single* sound relaxation whose error is small
on every sub-box of the range. One fit does it: Weierstrass on `[L, U]`, and a sub-box only sees
a subset of those points, so the sampled range never grows; `M` is bounded over the whole range
because `polyDerivRadius` is monotone in the box, so one sample count serves every sub-box.

## Inputs
* `σ` – activation function
* `σ'` – its derivative
* `L` – lower end of the range
* `U` – upper end of the range
* `Mσ` – bound on the derivative
* `ε` – accuracy

## Hypotheses
* `hd` – the activation has the given derivative
* `hσ` – the derivative is bounded
* `hε` – accuracy is positive

## Conclusion
* one sound relaxation has error below the accuracy on every box in the range

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every term is a magnitude, so the radius never goes below zero. -/
private theorem aux_polyDerivRadius_nonneg {k : ℕ} (c : Fin (k + 1) → ℝ)
    (l u : ℝ) : -- --- CONCL ---
    0 ≤ polyDerivRadius c l u := by -- --- PROOF ---
  have hmax : (0 : ℝ) ≤ max |l| |u| := le_trans (abs_nonneg l) (le_max_left _ _)
  show (0:ℝ) ≤ ∑ i : Fin (k + 1), if (i : ℕ) = 1 then 0
    else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : (i : ℕ) = 1
  · simp only [if_pos hi]
    exact le_refl 0
  · simp only [if_neg hi]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hmax _)

/-- A sub-box reaches no further from zero, so its radius is no larger. -/
private theorem aux_polyDerivRadius_mono {k : ℕ} (c : Fin (k + 1) → ℝ) {l u L U : ℝ}
    (hl : L ≤ l) (hlu : l ≤ u) (hu : u ≤ U) : -- --- CONCL ---
    polyDerivRadius c l u ≤ polyDerivRadius c L U := by -- --- PROOF ---
  have hLm : |L| ≤ max |L| |U| := le_max_left _ _
  have hUm : |U| ≤ max |L| |U| := le_max_right _ _
  have hL1 := neg_abs_le L
  have hU2 := le_abs_self U
  -- both ends of the sub-box lie between the outer box's, so neither is further out
  have hl' : |l| ≤ max |L| |U| := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hu' : |u| ≤ max |L| |U| := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmax : max |l| |u| ≤ max |L| |U| := max_le hl' hu'
  have hmax0 : (0 : ℝ) ≤ max |l| |u| := le_trans (abs_nonneg l) (le_max_left _ _)
  show (∑ i : Fin (k + 1), if (i : ℕ) = 1 then 0
      else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1))
    ≤ ∑ i : Fin (k + 1), if (i : ℕ) = 1 then 0
      else |c i| * (i : ℕ) * max |L| |U| ^ ((i : ℕ) - 1)
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : (i : ℕ) = 1
  · simp only [if_pos hi]
    exact le_refl 0
  · simp only [if_neg hi]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmax0 hmax _)
      (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- The bracket widened by a radius grows by at most that radius. -/
private theorem aux_polyDerivDiff_le {lo hi ctr rad r : ℝ} (hrad0 : 0 ≤ rad)
    (hrad : rad ≤ r) : -- --- CONCL ---
    polyDerivDiff lo hi ctr rad ≤ max |lo - ctr| |hi - ctr| + r := by -- --- PROOF ---
  have hA : |lo - ctr| ≤ max |lo - ctr| |hi - ctr| := le_max_left _ _
  have hB : |hi - ctr| ≤ max |lo - ctr| |hi - ctr| := le_max_right _ _
  have hA1 := neg_abs_le (lo - ctr)
  have hA2 := le_abs_self (lo - ctr)
  have hB1 := neg_abs_le (hi - ctr)
  have hB2 := le_abs_self (hi - ctr)
  show max |lo - ctr - rad| |hi - ctr + rad| ≤ max |lo - ctr| |hi - ctr| + r
  refine max_le ?_ ?_
  · rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  · rw [abs_le]
    exact ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_polyRelaxation_error_lt {σ σ' : ℝ → ℝ} {L U Mσ ε : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, |σ' x| ≤ Mσ) (hε : 0 < ε) : -- --- CONCL ---
    ∃ (k : ℕ) (P : CORALean.PolyRelaxation ℝ k), P.IsSound σ ∧ ∀ l u : ℝ,
      L ≤ l → l ≤ u → u ≤ U → P.error l u < ε := by -- --- PROOF ---
  have hcont : ContinuousOn σ (Set.Icc L U) :=
    fun x _ => ((hd x).continuousAt).continuousWithinAt
  obtain ⟨k, c₀, hfit⟩ := exists_evalPoly_near hcont (show (0:ℝ) < ε / 4 by linarith)
  -- the fit is fixed once and for all, so `M` is a function of the box alone
  have hM : ∀ l u x, l ≤ x → x ≤ u → |σ' x - evalPolyDeriv c₀ x|
      ≤ polyDerivDiff (-Mσ) Mσ (polyDerivCenter c₀) (polyDerivRadius c₀ l u) := by
    intro l u x hx hx'
    obtain ⟨h₁, h₂⟩ := abs_le.mp (hσ x)
    exact abs_sub_evalPolyDeriv_le h₁ h₂ hx hx'
  obtain ⟨Mmax, hMmax0, hMle⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ l u : ℝ, L ≤ l → l ≤ u → u ≤ U →
      polyDerivDiff (-Mσ) Mσ (polyDerivCenter c₀) (polyDerivRadius c₀ l u) ≤ M := by
    refine ⟨max |(-Mσ) - polyDerivCenter c₀| |Mσ - polyDerivCenter c₀|
      + polyDerivRadius c₀ L U, ?_, fun l u hl hlu hu => aux_polyDerivDiff_le
        (aux_polyDerivRadius_nonneg c₀ l u) (aux_polyDerivRadius_mono c₀ hl hlu hu)⟩
    have h1 := aux_polyDerivRadius_nonneg c₀ L U
    have h2 : (0:ℝ) ≤ max |(-Mσ) - polyDerivCenter c₀| |Mσ - polyDerivCenter c₀| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    linarith
  -- one sample count for every sub-box, which the bound on `M` is what allows
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max 1 (2 * (Mmax * (U - L)) / ε))
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (le_trans zero_le_one (le_max_left _ _)) hNgt
  have hN : 0 < N := Nat.cast_pos.mp hNpos
  have hinv : (0:ℝ) ≤ 1 / N := le_of_lt (one_div_pos.mpr hNpos)
  have hpad : Mmax * ((U - L) / N) < ε / 2 := by
    have h2 : 2 * (Mmax * (U - L)) / ε < N := lt_of_le_of_lt (le_max_right _ _) hNgt
    rw [div_lt_iff₀ hε] at h2
    rw [← mul_div_assoc, div_lt_iff₀ hNpos]
    linarith
  refine ⟨k, PolyRelaxation.ofSampling σ (fun _ _ => c₀)
    (fun l u => polyDerivDiff (-Mσ) Mσ (polyDerivCenter c₀) (polyDerivRadius c₀ l u))
    (fun _ _ => N), PolyRelaxation.ofSampling_sound hd _ _ _ hM (fun _ _ => hN), ?_⟩
  intro l u hl hlu hu
  -- every sample of a sub-box is a point of `[L, U]`, so the fit's own bound caps it
  have hgrid : ∀ i : Fin (N + 1),
      |σ (sampleGrid l u N i) - evalPoly c₀ (sampleGrid l u N i)| ≤ ε / 4 := by
    intro i
    obtain ⟨ha, hb⟩ := sampleGrid_mem_Icc hN hlu i
    exact hfit _ (le_trans hl ha) (le_trans hb hu)
  have hsup : sampleSup (fun x => σ x - evalPoly c₀ x) l u N ≤ ε / 4 :=
    Finset.sup'_le _ _ fun i _ => (abs_le.mp (hgrid i)).2
  have hinf : -(ε / 4) ≤ sampleInf (fun x => σ x - evalPoly c₀ x) l u N :=
    Finset.le_inf' _ _ fun i _ => (abs_le.mp (hgrid i)).1
  have hM0 : (0:ℝ) ≤ polyDerivDiff (-Mσ) Mσ (polyDerivCenter c₀) (polyDerivRadius c₀ l u) :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  -- the padding at this box is under the padding at the whole range
  have hstep : polyDerivDiff (-Mσ) Mσ (polyDerivCenter c₀) (polyDerivRadius c₀ l u)
      * ((u - l) / N) ≤ Mmax * ((U - L) / N) := by
    have heq1 : (u - l) / (N:ℝ) = (u - l) * (1 / N) := by ring
    have heq2 : (U - L) / (N:ℝ) = (U - L) * (1 / N) := by ring
    rw [heq1, heq2]
    exact mul_le_mul (hMle l u hl hlu hu)
      (mul_le_mul_of_nonneg_right (by linarith) hinv)
      (mul_nonneg (by linarith) hinv) hMmax0
  show (sampleSup (fun x => σ x - evalPoly c₀ x) l u N
      - sampleInf (fun x => σ x - evalPoly c₀ x) l u N) / 2
    + polyDerivDiff (-Mσ) Mσ (polyDerivCenter c₀) (polyDerivRadius c₀ l u) * ((u - l) / N) < ε
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
