module

public import CORALean.ContSet.Zonotope.Real.Theorems.NaiveVertexSampleLe
public import CORALean.Global.ShenmaierHalfspace
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# Naive vertex sampling's accuracy, at a fixed `ε`

`[1, Cor. 4.7]`, second half, as it holds: for `ε ∈ (0, 1]`, `N` independent uniform sign
vectors reach `(1 - ε) r(Ẑ, Ê)` with probability at least `P_S(ε)`, at `ϑ = 0` and the
dimension `n` of `P_S` the number `m` of generators, which is that of the sign cube sampled.
The maximum is attained at one corner (`Sec. III`), which a sample is with probability
`2⁻ᵐ ≥ (ε / (2 + ε))ᵐ`. The printed `Ẑ ⊆ Ê` with probability at least `P_S(1 - r_vs)` chooses
`ε` after the samples are drawn and reads a statement about them as one about the sets.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory ProbabilityTheory

variable {n N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.naive_vertex_sample_prob (Z : Zonotope (Vec ℝ n)) (H : E →ₗ[ℝ] Vec ℝ n)
    (hH : Function.Surjective H) (d : Vec ℝ n) {r : ℝ}
    (hr : IsGreatest ((fun p => coeffNorm H (p - d)) '' Z.construct) r)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hN : 0 < N)
    (a : Fin N → Ω → (Fin Z.h → Bool)) (hm : ∀ i, Measurable (a i)) (hind : iIndepFun a P)
    (hu : ∀ i σ, P.real (a i ⁻¹' {σ}) = 1 / 2 ^ Z.h) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : -- --- STMT ---
    ENNReal.ofReal (shenmaierProb Z.h N 0 ε)
      ≤ P {ω | (1 - ε) * r ≤ Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
        fun i => coeffNorm H (Z.corner (a i ω) - d)} := by -- --- PROOF ---
  -- the maximum is attained at a corner
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    fun σ => coeffNorm H (Z.corner σ - d)
  have hrσ : r = coeffNorm H (Z.corner σ - d) :=
    (hr.unique (Zonotope.isGreatest_coeffNorm_corner Z H hH d)).trans hσ
  have hr0 : 0 ≤ r := by
    obtain ⟨p, -, hp⟩ := hr.1
    exact hp ▸ coeffNorm_nonneg H _
  -- some sample is that corner, a subset of the event
  set S := (⋂ i, a i ⁻¹' {σ}ᶜ)ᶜ with hS
  have hsub : S ⊆ {ω | (1 - ε) * r ≤ Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      fun i => coeffNorm H (Z.corner (a i ω) - d)} := by
    intro ω hω
    simp only [hS, Set.mem_compl_iff, Set.mem_iInter, not_forall] at hω
    obtain ⟨i, hi⟩ := hω
    refine le_trans ?_ (Finset.le_sup' (fun i => coeffNorm H (Z.corner (a i ω) - d))
      (Finset.mem_univ i))
    have : a i ω = σ := by simpa using hi
    rw [this, ← hrσ]
    nlinarith
  refine le_trans ?_ (measure_mono hsub)
  have hmeas : ∀ i, MeasurableSet (a i ⁻¹' {σ}ᶜ) := fun i =>
    (hm i) (measurableSet_singleton σ).compl
  -- independence: no sample is the corner with probability `(1 - 2⁻ᵐ)ᴺ`
  have hind' : P (⋂ i, a i ⁻¹' {σ}ᶜ) = ∏ i, P (a i ⁻¹' {σ}ᶜ) := by
    have := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => ({σ}ᶜ : Set (Fin Z.h → Bool))) fun i _ => (measurableSet_singleton σ).compl
    simpa using this
  have hreal : P.real (⋂ i, a i ⁻¹' {σ}ᶜ) = (1 - 1 / 2 ^ Z.h) ^ N := by
    rw [Measure.real, hind', ENNReal.toReal_prod]
    have : ∀ i, (P (a i ⁻¹' {σ}ᶜ)).toReal = 1 - 1 / 2 ^ Z.h := fun i => by
      rw [← Measure.real, Set.preimage_compl, probReal_compl_eq_one_sub (hm i
        (measurableSet_singleton σ)), hu]
    rw [Finset.prod_congr rfl fun i _ => this i]
    simp
  have hSreal : P.real S = 1 - (1 - 1 / 2 ^ Z.h) ^ N := by
    rw [hS, probReal_compl_eq_one_sub (MeasurableSet.iInter hmeas), hreal]
  -- the bound `P_S(ε)` is below it since `ε / (2 + ε) ≤ 1 / 2`
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [← Measure.real, hSreal, shenmaierProb]
  have h1 : (ε / (2 + ε)) ^ Z.h ≤ 1 / 2 ^ Z.h := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ (by positivity)]; nlinarith) _
  have h2 : (0 : ℝ) ≤ 1 - 1 / 2 ^ Z.h := sub_nonneg.mpr (by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 ^ Z.h)]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h3 : (1 : ℝ) - 1 / 2 ^ Z.h ≤ 1 - (ε / (2 + ε)) ^ Z.h + 0 := by linarith
  have := pow_le_pow_left₀ h2 h3 N
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
