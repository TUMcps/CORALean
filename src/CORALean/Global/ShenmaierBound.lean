import CORALean.Global.ThetaUniform
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Shenmaier's sampling bound

`[1, Thm. 4.2]`: for a compact `K`, a norm `‖·‖` with unit ball `B`, and `N` independent
`ϑ`-uniform samples `vᵢ ∈ B` with `zᵢ = argmax_{z ∈ B*} zᵀvᵢ`, the value
`r_S = maxᵢ max_{x ∈ K} zᵢᵀ x` never exceeds `max_K ‖x‖` (Eq. 16), and for every
`ε ∈ (0, 1]` reaches `(1 - ε) max_K ‖x‖` with probability at least
`P_S(ε) = 1 - (1 - (ε / (2 + ε))ⁿ + ϑ)^N` (Eq. 17-18). The norm is any function with the
norm laws, continuous and above a multiple of the ambient norm, so that its ball is a
compact body; `zᵢ ∈ B*` with `zᵢ vᵢ = ‖vᵢ‖` is what the argmax gives. The proof is the
paper's: a sample landing in `(1 + ε/2)⁻¹ (χ + (ε/2) B)`, `χ` the direction of the far point,
forces `zᵢ χ ≥ 1 - ε`, and the samples all miss that set with probability at most
`(1 - (ε/(2+ε))ⁿ + ϑ)^N`. `P_S(ε) < 0` reads `0`, as `ENNReal.ofReal` does; `ϑ ≥ 0`.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory Pointwise

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section Laws

variable (nrm : E → ℝ) (hadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y)
  (hsmul : ∀ (a : ℝ) x, nrm (a • x) = |a| * nrm x)

include hadd hsmul in
theorem aux_nrm_nonneg (x : E) : 0 ≤ nrm x := by -- --- PROOF ---
  have h0 : nrm 0 = 0 := by simpa using hsmul 0 x
  have h1 := hadd x (-x)
  have h2 := hsmul (-1) x
  simp only [add_neg_cancel, h0, neg_smul, one_smul, abs_neg, abs_one, one_mul] at h1 h2
  linarith

include hadd hsmul in
/-- A functional in the dual ball is below the norm everywhere. -/
theorem aux_le_nrm (hdef : ∀ x, nrm x = 0 → x = 0) (z : E →L[ℝ] ℝ)
    (hz : ∀ x, nrm x ≤ 1 → z x ≤ 1) (x : E) : z x ≤ nrm x := by -- --- PROOF ---
  rcases (aux_nrm_nonneg nrm hadd hsmul x).lt_or_eq with hpos | hzero
  · have := hz ((nrm x)⁻¹ • x) (by rw [hsmul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne'])
    rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hpos, mul_one] at this
    exact this
  · rw [hdef x hzero.symm, map_zero]
    exact aux_nrm_nonneg nrm hadd hsmul 0

include hsmul in
/-- The ball of radius `r > 0` is `r` times the unit ball. -/
theorem aux_ball_eq_smul {r : ℝ} (hr : 0 < r) :
    {x | nrm x ≤ r} = r • {x : E | nrm x ≤ 1} := by -- --- PROOF ---
  ext x
  rw [Set.mem_smul_set]
  constructor
  · intro hx
    refine ⟨r⁻¹ • x, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    show nrm (r⁻¹ • x) ≤ 1
    rw [hsmul, abs_inv, abs_of_pos hr, inv_mul_le_iff₀ hr, mul_one]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    show nrm (r • y) ≤ r
    rw [hsmul, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hy

include hadd hsmul in
/-- A sample near `χ` puts its maximizer within `ε` of `1` at `χ`: the paper's Appendix A. -/
theorem aux_dir_ge (z : E →L[ℝ] ℝ) (hle : ∀ x, z x ≤ nrm x) {χ y : E} (hχn : nrm χ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hyS : nrm ((1 + ε / 2) • y - χ) ≤ ε / 2)
    (hyB : nrm y ≤ 1) (hzv' : z y = nrm y) : 1 - ε ≤ z χ := by -- --- PROOF ---
  have hlowr : 1 - ε / 2 ≤ (1 + ε / 2) * nrm y := by
    have h1 := hadd ((1 + ε / 2) • y) (χ - (1 + ε / 2) • y)
    rw [add_sub_cancel, hχn, hsmul, abs_of_pos (by linarith)] at h1
    have h2 : nrm (χ - (1 + ε / 2) • y) = nrm ((1 + ε / 2) • y - χ) := by
      rw [← neg_sub, show -((1 + ε / 2) • y - χ) = (-1 : ℝ) • ((1 + ε / 2) • y - χ) by simp,
        hsmul]; simp
    linarith
  have hypos : 0 < nrm y := by
    by_contra hy0
    have : (1 + ε / 2) * nrm y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (not_lt.mp hy0)
    linarith
  set w := (nrm y)⁻¹ • y with hw
  have hzw : z w = 1 := by
    rw [hw, map_smul, smul_eq_mul, hzv', inv_mul_cancel₀ hypos.ne']
  -- `‖χ - w‖ ≤ ε`, through `(1 + ε/2) y`
  have hdist : nrm (w - χ) ≤ ε := by
    have hsplit := hadd ((1 + ε / 2) • y - χ) (w - (1 + ε / 2) • y)
    rw [show (1 + ε / 2) • y - χ + (w - (1 + ε / 2) • y) = w - χ by abel] at hsplit
    have hwy : w - (1 + ε / 2) • y = ((nrm y)⁻¹ - (1 + ε / 2)) • y := by
      rw [hw, sub_smul]
    rw [hwy, hsmul] at hsplit
    have habs : |(nrm y)⁻¹ - (1 + ε / 2)| * nrm y ≤ ε / 2 := by
      rw [← abs_of_pos hypos, ← abs_mul, abs_of_pos hypos, sub_mul,
        inv_mul_cancel₀ hypos.ne', abs_le]
      constructor <;> nlinarith
    linarith
  have hzχ : 1 - ε ≤ z χ := by
    have := hle (w - χ)
    rw [map_sub, hzw] at this
    linarith
  exact hzχ

end Laws


-- =======================================  MAIN THEOREM  ======================================= --

theorem shenmaier_bound [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (nrm : E → ℝ)
    (hadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y)
    (hsmul : ∀ (a : ℝ) x, nrm (a • x) = |a| * nrm x) (hcont : Continuous nrm) {C : ℝ}
    (hC : 0 < C) (hlow : ∀ x, C * ‖x‖ ≤ nrm x) (vol : Measure E) [vol.IsAddHaarMeasure]
    {K : Set E} {M : ℝ} (hM : IsGreatest (nrm '' K) M)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}
    (v : Fin N → Ω → E) (hvm : ∀ i, Measurable (v i)) (hind : iIndepFun v P) {ϑ : ℝ}
    (hϑ : 0 ≤ ϑ) (hunif : ∀ i, IsThetaUniform P (v i) vol {x | nrm x ≤ 1} ϑ)
    (z : Fin N → Ω → E →L[ℝ] ℝ) (hzB : ∀ i ω x, nrm x ≤ 1 → z i ω x ≤ 1)
    (hzv : ∀ i ω, z i ω (v i ω) = nrm (v i ω)) (rS : Ω → ℝ)
    (hrS : ∀ ω, IsGreatest {t | ∃ i, ∃ x ∈ K, t = z i ω x} (rS ω)) :
    (∀ ω, rS ω ≤ M) ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ENNReal.ofReal (1 - (1 - (ε / (2 + ε)) ^ Module.finrank ℝ E + ϑ) ^ N)
        ≤ P {ω | (1 - ε) * M ≤ rS ω} := by -- --- PROOF ---
  have hnn := aux_nrm_nonneg nrm hadd hsmul
  have hdef : ∀ x, nrm x = 0 → x = 0 := fun x hx => by
    have := hlow x
    rw [hx] at this
    exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg x]) (norm_nonneg x))
  have hle := fun i ω => aux_le_nrm nrm hadd hsmul hdef (z i ω) (hzB i ω)
  -- `(16)`: every value is some `zᵢ x ≤ ‖x‖ ≤ M`
  have h16 : ∀ ω, rS ω ≤ M := by
    intro ω
    obtain ⟨i, x, hx, he⟩ := (hrS ω).1
    rw [he]
    exact (hle i ω x).trans (hM.2 ⟨x, hx, rfl⟩)
  refine ⟨h16, fun ε hε hε1 => ?_⟩
  set n := Module.finrank ℝ E with hn
  set q := 1 - (ε / (2 + ε)) ^ n + ϑ with hq
  have hratio1 : (ε / (2 + ε)) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  have hq0 : 0 ≤ q := by linarith
  have hfinal : ENNReal.ofReal (1 - q ^ N) ≤ 1 - ENNReal.ofReal q ^ N := by
    rw [ENNReal.ofReal_sub 1 (pow_nonneg hq0 N), ENNReal.ofReal_one, ENNReal.ofReal_pow hq0]
  obtain ⟨xm, hxmK, hxmM⟩ := hM.1
  rcases (hxmM ▸ hnn xm : 0 ≤ M).lt_or_eq with hMpos | hM0
  swap
  -- `M = 0`: `K = {0}`, every value is `0`, and the event is certain
  · have hall : {ω | (1 - ε) * M ≤ rS ω} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, ← hM0, mul_zero]
      obtain ⟨i, x, hx, he⟩ := (hrS ω).1
      have hx0 : x = 0 := hdef x (le_antisymm (hM0 ▸ hM.2 ⟨x, hx, rfl⟩) (hnn x))
      rw [he, hx0, map_zero]
    rw [hall, measure_univ]
    exact (hfinal.trans tsub_le_self)
  -- `M > 0`: the far point's direction `χ`, and the target set `S` around it
  set χ := M⁻¹ • xm with hχ
  have hχn : nrm χ = 1 := by
    rw [hχ, hsmul, abs_inv, abs_of_pos hMpos, hxmM, inv_mul_cancel₀ hMpos.ne']
  set B := {x : E | nrm x ≤ 1} with hB
  set S := {y : E | nrm ((1 + ε / 2) • y - χ) ≤ ε / 2} with hS
  have hSmeas : MeasurableSet S :=
    (isClosed_le (hcont.comp ((continuous_const_smul _).sub continuous_const))
      continuous_const).measurableSet
  -- a point of `S` lies in `B`: `(1 + ε/2) ‖y‖ ≤ ‖χ‖ + ε/2`
  have hSB : S ⊆ B := by
    intro y hy
    have h1 := hadd ((1 + ε / 2) • y - χ) χ
    rw [sub_add_cancel, hsmul, abs_of_pos (by linarith), hχn] at h1
    show nrm y ≤ 1
    have hy' : nrm ((1 + ε / 2) • y - χ) ≤ ε / 2 := hy
    have : (1 + ε / 2) * nrm y ≤ (1 + ε / 2) * 1 := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  -- a sample in `S` makes `zᵢ χ ≥ 1 - ε`, so `r_S ≥ (1 - ε) M`
  have hgood : ∀ i ω, v i ω ∈ S → (1 - ε) * M ≤ rS ω := by
    intro i ω hvS
    have hzχ : 1 - ε ≤ z i ω χ := aux_dir_ge nrm hadd hsmul (z i ω) (hle i ω) hχn hε hε1 hvS
      (hSB hvS) (hzv i ω)
    have hxm : z i ω xm = M * z i ω χ := by
      rw [hχ, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hMpos.ne', one_mul]
    calc (1 - ε) * M ≤ z i ω χ * M := mul_le_mul_of_nonneg_right hzχ hMpos.le
      _ = z i ω xm := by rw [hxm, mul_comm]
      _ ≤ rS ω := (hrS ω).2 ⟨i, xm, hxmK, rfl⟩
  -- `B` is a compact body: closed, inside a ball, around an open set holding `0`
  have hBclosed : IsClosed B := isClosed_le hcont continuous_const
  have hBbdd : B ⊆ Metric.closedBall 0 (1 / C) := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hC]
    have := hlow x
    have hx' : nrm x ≤ 1 := hx
    nlinarith
  have hBfin : vol B ≠ ⊤ :=
    ((isCompact_closedBall 0 (1 / C)).of_isClosed_subset hBclosed hBbdd).measure_lt_top.ne
  have hBpos : vol B ≠ 0 := by
    have hopen : IsOpen {x : E | nrm x < 1} := isOpen_lt hcont continuous_const
    have h0 : (0 : E) ∈ {x : E | nrm x < 1} := by
      show nrm 0 < 1
      rw [show nrm 0 = 0 by simpa using hsmul 0 0]
      exact zero_lt_one
    exact pos_iff_ne_zero.mp ((hopen.measure_pos vol ⟨0, h0⟩).trans_le
      (measure_mono fun x (hx : nrm x < 1) => (le_of_lt hx : nrm x ≤ 1)))
  -- `S` is `B` shrunk by `(1 + ε/2)⁻¹`, scaled by `ε/2` and moved: its share is `(ε/(2+ε))ⁿ`
  have hball : ∀ r : ℝ, 0 < r → vol {x | nrm x ≤ r} = ENNReal.ofReal (r ^ n) * vol B := by
    intro r hr
    rw [aux_ball_eq_smul nrm hsmul hr, Measure.addHaar_smul, abs_of_pos (by positivity)]
  have hSeq : S = (fun y => (1 + ε / 2) • y) ⁻¹' ((fun u => u + -χ) ⁻¹' {w | nrm w ≤ ε / 2}) := by
    ext y
    simp [hS, sub_eq_add_neg]
  have hvolS : vol S = ENNReal.ofReal |((1 + ε / 2) ^ n)⁻¹|
      * (ENNReal.ofReal ((ε / 2) ^ n) * vol B) := by
    rw [hSeq, Measure.addHaar_preimage_smul vol (by positivity : (1 + ε / 2) ≠ 0),
      measure_preimage_add_right, hball _ (by positivity)]
  have hBr : 0 < (vol B).toReal := ENNReal.toReal_pos hBpos hBfin
  have hratio : (vol S).toReal / (vol B).toReal = (ε / (2 + ε)) ^ n := by
    rw [hvolS, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (by positivity), mul_div_assoc,
      mul_div_cancel_right₀ _ hBr.ne', ← div_eq_inv_mul, ← div_pow]
    congr 1
    field_simp
  -- each sample misses `S` with probability at most `q`
  have hmiss : ∀ i, P (v i ⁻¹' Sᶜ) ≤ ENNReal.ofReal q := by
    intro i
    have hu := (abs_le.mp ((hunif i).2 S hSB hSmeas)).1
    rw [hratio] at hu
    rw [Set.preimage_compl, prob_compl_eq_one_sub (hvm i hSmeas)]
    rw [← ENNReal.ofReal_toReal (a := 1 - P (v i ⁻¹' S)) (ENNReal.sub_ne_top ENNReal.one_ne_top)]
    apply ENNReal.ofReal_le_ofReal
    rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    linarith
  -- independence: all of them miss with probability at most `q^N`
  have hinter : P (⋂ i ∈ (Finset.univ : Finset (Fin N)), v i ⁻¹' Sᶜ) = ∏ i, P (v i ⁻¹' Sᶜ) :=
    hind.measure_inter_preimage_eq_mul Finset.univ fun i _ => hSmeas.compl
  have hprod : ∏ i, P (v i ⁻¹' Sᶜ) ≤ ENNReal.ofReal q ^ N := by
    calc ∏ i, P (v i ⁻¹' Sᶜ) ≤ ∏ _i : Fin N, ENNReal.ofReal q :=
          Finset.prod_le_prod' fun i _ => hmiss i
      _ = ENNReal.ofReal q ^ N := by simp
  have hmeas : MeasurableSet (⋂ i ∈ (Finset.univ : Finset (Fin N)), v i ⁻¹' Sᶜ) :=
    Finset.measurableSet_biInter _ fun i _ => hvm i hSmeas.compl
  have hsub : (⋂ i ∈ (Finset.univ : Finset (Fin N)), v i ⁻¹' Sᶜ)ᶜ
      ⊆ {ω | (1 - ε) * M ≤ rS ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_preimage, not_forall, not_not] at hω
    obtain ⟨i, -, hi⟩ := hω
    exact hgood i ω hi
  calc ENNReal.ofReal (1 - q ^ N) ≤ 1 - ENNReal.ofReal q ^ N := hfinal
    _ ≤ 1 - P (⋂ i ∈ (Finset.univ : Finset (Fin N)), v i ⁻¹' Sᶜ) :=
        tsub_le_tsub_left (hinter ▸ hprod) 1
    _ = P (⋂ i ∈ (Finset.univ : Finset (Fin N)), v i ⁻¹' Sᶜ)ᶜ := (prob_compl_eq_one_sub hmeas).symm
    _ ≤ P {ω | (1 - ε) * M ≤ rS ω} := measure_mono hsub

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
