module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.GadgetH
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# The norm of the gadget zonotope

The zonotope `Z(½H)` of the reduction behind [1, Thm. 21], `H` of [1, Eq. 63], has the norm
`‖(y, h)‖_{Z(½H)} = max(‖y‖_∞, (‖y‖₁ + |h|) / n)`: its unit ball is
`{(y, h) | ‖y‖_∞ ≤ 1, ‖y‖₁ + |h| ≤ n}`, a double pyramid over the cube's cross-polytope
slices. Each row pair `½(β₁ᵢ - β₂ᵢ)`, `½(β₁ᵢ + β₂ᵢ)` is bounded by `max(|β₁ᵢ|, |β₂ᵢ|)` in both
combinations, which is the lower bound; a preimage of that norm spreads `h` over the rows in
proportion to their slack `μ - |yᵢ|`. This closed form is what [1, Lemma 25], [1, Lemma 27]
and [1, Prop. 28] are read from here; `½H` is onto, so the norm is defined everywhere.

## Inputs
* none

## Hypotheses
* `hn` – the dimension is at least one

## Conclusion
* half the gadget matrix is onto and its coefficient norm has a closed form

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


/-- The map applied: `½H (β₁, β₂) = (½(β₁ - β₂), ½(1ᵀβ₁ + 1ᵀβ₂))`. -/
theorem half_gadgetH_apply (β : Vec ℝ n × Vec ℝ n) :
    ((1 / 2 : ℝ) • gadgetH n) β =
      ((1 / 2 : ℝ) • (β.1 - β.2), (1 / 2 : ℝ) * (∑ i, β.1 i + ∑ i, β.2 i)) := rfl


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A preimage of `(y, h)` whose norm is the closed form. -/
private theorem aux_exists_preimage (hn : 1 ≤ n) (y : Vec ℝ n) (h : ℝ) : -- --- CONCL ---
    ∃ β : Vec ℝ n × Vec ℝ n, ((1 / 2 : ℝ) • gadgetH n) β = (y, h) ∧
      ‖β‖ ≤ max ‖y‖ ((∑ i, |y i| + |h|) / n) := by -- --- PROOF ---
  set μ := max ‖y‖ ((∑ i, |y i| + |h|) / n) with hμ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hyi : ∀ i, |y i| ≤ μ := fun i =>
    ((norm_le_pi_norm y i).trans (le_max_left _ _)).trans_eq' (Real.norm_eq_abs _).symm
  -- the slack `D = nμ - ‖y‖₁` covers `|h|`
  set D := n * μ - ∑ i, |y i| with hD
  have hDh : |h| ≤ D := by
    have : (∑ i, |y i| + |h|) / n ≤ μ := le_max_right _ _
    rw [div_le_iff₀ hnpos] at this
    rw [hD]; linarith
  -- `h` spread over the rows in proportion to their slack `μ - |yᵢ|`
  let t : Vec ℝ n := fun i => if D = 0 then 0 else h * (μ - |y i|) / D
  have ht : ∀ i, |t i| ≤ μ - |y i| := by
    intro i
    by_cases h0 : D = 0
    · simp only [t, h0, if_true, abs_zero]; linarith [hyi i]
    · have hDpos : 0 < D := lt_of_le_of_ne ((abs_nonneg h).trans hDh) (Ne.symm h0)
      simp only [t, h0, if_false, abs_div, abs_mul, abs_of_pos hDpos,
        abs_of_nonneg (sub_nonneg.mpr (hyi i))]
      rw [div_le_iff₀ hDpos]
      nlinarith [sub_nonneg.mpr (hyi i)]
  have hsum : ∑ i, t i = h := by
    by_cases h0 : D = 0
    · simp only [t, h0, if_true, Finset.sum_const_zero]
      rw [h0] at hDh; exact (abs_nonpos_iff.mp hDh).symm
    · simp only [t, h0, if_false]
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hD, mul_div_assoc, div_self h0,
        mul_one]
  -- `β = (y + t, -y + t)` maps to `(y, Σ t) = (y, h)`, each entry within `μ`
  refine ⟨(y + t, -y + t), ?_, ?_⟩
  · rw [half_gadgetH_apply]
    refine Prod.ext ?_ ?_
    · funext i; simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
        smul_eq_mul]; ring
    · simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        hsum]; ring
  · have hμ0 : 0 ≤ μ := (norm_nonneg y).trans (le_max_left _ _)
    refine max_le ?_ ?_ <;> refine (pi_norm_le_iff_of_nonneg hμ0).mpr fun i => ?_ <;>
      simp only [Pi.add_apply, Pi.neg_apply, Real.norm_eq_abs]
    · exact (abs_add_le _ _).trans (by linarith [ht i])
    · exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith [ht i])

/-- Every preimage is at least as long as the closed form. -/
private theorem aux_le_norm_of_apply (hn : 1 ≤ n) (y : Vec ℝ n) (h : ℝ) (β : Vec ℝ n × Vec ℝ n)
    (hβ : ((1 / 2 : ℝ) • gadgetH n) β = (y, h)) : -- --- CONCL ---
    max ‖y‖ ((∑ i, |y i| + |h|) / n) ≤ ‖β‖ := by -- --- PROOF ---
  rw [half_gadgetH_apply, Prod.ext_iff] at hβ
  obtain ⟨hy, hh⟩ := hβ
  simp only at hy hh
  have hb1 : ∀ i, |β.1 i| ≤ ‖β‖ := fun i =>
    ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm β.1 i)).trans (norm_fst_le β)
  have hb2 : ∀ i, |β.2 i| ≤ ‖β‖ := fun i =>
    ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm β.2 i)).trans (norm_snd_le β)
  have hyi : ∀ i, y i = (1 / 2) * (β.1 i - β.2 i) := fun i => by
    rw [← hy]; simp [mul_sub]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine max_le ((pi_norm_le_iff_of_nonneg (norm_nonneg β)).mpr fun i => ?_) ?_
  · rw [Real.norm_eq_abs, hyi i]
    have := hb1 i; have := hb2 i
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [abs_sub (β.1 i) (β.2 i)]
  · rw [div_le_iff₀ hnpos]
    -- row by row, `½|a - b| ± ½(a + b)` is `max(a, b)` or `max(-a, -b)`
    have hrow : ∀ (s : ℝ), s = 1 ∨ s = -1 → ∀ i,
        |y i| + s * ((1 / 2) * (β.1 i + β.2 i)) ≤ ‖β‖ := by
      intro s hs i
      rw [hyi i]
      have h1 := abs_le.mp (hb1 i); have h2 := abs_le.mp (hb2 i)
      rcases hs with rfl | rfl <;>
        rcases abs_cases ((1 / 2) * (β.1 i - β.2 i)) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
        · rw [ha]; linarith
    have hsplit : ∀ s : ℝ, s * h = ∑ i, s * ((1 / 2) * (β.1 i + β.2 i)) := fun s => by
      rw [← hh, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    rcases abs_cases h with ⟨hab, -⟩ | ⟨hab, -⟩
    · have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow 1 (Or.inl rfl) i
      rw [Finset.sum_add_distrib, ← hsplit 1, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at this
      rw [hab]; linarith
    · have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow (-1) (Or.inr rfl) i
      rw [Finset.sum_add_distrib, ← hsplit (-1), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at this
      rw [hab]; linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem coeffNorm_half_gadgetH (hn : 1 ≤ n) : -- --- CONCL ---
    Function.Surjective ((1 / 2 : ℝ) • gadgetH n) ∧
      ∀ (y : Vec ℝ n) (h : ℝ),
        coeffNorm ((1 / 2 : ℝ) • gadgetH n) (y, h) =
          max ‖y‖ ((∑ i, |y i| + |h|) / n) := by -- --- PROOF ---
  refine ⟨fun x => ?_, fun y h => le_antisymm ?_ ?_⟩
  · obtain ⟨β, hβ, -⟩ := aux_exists_preimage hn x.1 x.2
    exact ⟨β, hβ⟩
  · obtain ⟨β, hβ, hle⟩ := aux_exists_preimage hn y h
    exact (hβ ▸ coeffNorm_le _ β).trans hle
  · obtain ⟨β, hβ, he⟩ := exists_coeffNorm_eq ((1 / 2 : ℝ) • gadgetH n)
      (let ⟨β, hβ, _⟩ := aux_exists_preimage hn y h; ⟨β, hβ⟩)
    exact he ▸ aux_le_norm_of_apply hn y h β hβ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
