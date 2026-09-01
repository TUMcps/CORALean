import CORALean.ContDynamics.LinearSys.Operations
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# The input reach set splits at any intermediate time

Althoff's Prop. 3.2, in the direction the enclosures need: concatenating an
input over `[0,a]` with one over `[0,b]` gives an input over `[0,a+b]`, and what
it contributes is `e^{Ab}` applied to the first contribution plus the second.

The thesis states this as an equality; only `⊇` is used downstream, and it is
the direction that has to build an input rather than take one apart.

`Matrix` is a plain `def`, so instance search finds no metrizable structure on it
and a matrix-valued factor never gets `Continuous.aestronglyMeasurable`;
`aestronglyMeasurable_mulVec` goes one entry at a time instead. Moving an input
to a different window is then measure-preserving reflection and translation.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

/-- A continuous matrix applied to a measurable vector, entry by entry. -/
theorem aestronglyMeasurable_mulVec {M : ℝ → Mat ℝ n n} {v : ℝ → Vec ℝ n} {μ : Measure ℝ}
    (hM : Continuous M) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun s => M s *ᵥ v s) μ := by
  have hvk : ∀ k, AEStronglyMeasurable (fun s => v s k) μ := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (aemeasurable_pi_iff.mp (aestronglyMeasurable_iff_aemeasurable.mp hv)) k
  rw [aestronglyMeasurable_iff_aemeasurable]
  refine aemeasurable_pi_iff.mpr fun j => ?_
  have hj : ∀ s : ℝ, (M s *ᵥ v s) j = ∑ k, M s j k * v s k := fun _ => rfl
  simp only [hj]
  rw [← aestronglyMeasurable_iff_aemeasurable]
  -- `Finset.aestronglyMeasurable_sum` sums functions, the goal sums values
  have heq : (∑ k : Fin n, (fun s : ℝ => M s j k * v s k))
      = fun s : ℝ => ∑ k, M s j k * v s k := by
    funext s
    simp only [Finset.sum_apply]
  rw [← heq]
  exact Finset.aestronglyMeasurable_sum _ fun k _ =>
    ((hM.matrix_elem j k).aestronglyMeasurable).mul (hvk k)

/-- Lebesgue measure is invariant under negation. Taken from the scaling law at
`-1`: the negation-invariance instance itself sits behind Haar uniqueness, an
import far heavier than the one fact needed here. -/
theorem aux_measurePreserving_neg : MeasurePreserving (fun x : ℝ => -x) volume volume := by
  refine ⟨measurable_neg, ?_⟩
  have h := Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num)
  simpa using h

/-- Reflection is negation followed by a translation, and both preserve the
measure. -/
theorem aux_measurePreserving_sub_left (c : ℝ) :
    MeasurePreserving (fun σ : ℝ => c - σ) volume volume := by
  have h := (measurePreserving_add_left volume c).comp aux_measurePreserving_neg
  simpa [Function.comp_def, sub_eq_add_neg] using h

/-- Reflecting about `c` carries `Icc a b` onto `Icc (c-b) (c-a)` and preserves
Lebesgue measure. -/
theorem aestronglyMeasurable_comp_sub_left {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun σ => f (c - σ)) (volume.restrict (Set.Icc (c - b) (c - a))) := by
  have hpre : (fun σ : ℝ => c - σ) ⁻¹' Set.Icc a b = Set.Icc (c - b) (c - a) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => c - σ)
      (volume.restrict (Set.Icc (c - b) (c - a))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (aux_measurePreserving_sub_left c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp

/-- Translating by `c` carries `Icc a b` onto `Icc (a+c) (b+c)` and preserves
Lebesgue measure. -/
theorem aestronglyMeasurable_comp_sub_right {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun σ => f (σ - c)) (volume.restrict (Set.Icc (a + c) (b + c))) := by
  have hpre : (fun σ : ℝ => σ - c) ⁻¹' Set.Icc a b = Set.Icc (a + c) (b + c) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => σ - c)
      (volume.restrict (Set.Icc (a + c) (b + c))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (measurePreserving_sub_right volume c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp

/-- The integrand of an input solution is continuous in its matrix factor. -/
theorem aux_continuous_expSub (A : Mat ℝ n n) (c : ℝ) :
    Continuous fun s : ℝ => exp ((c - s) • A) :=
  exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)

/-- The reflected form `inputSolution_outer` states its hypothesis in, from the
plain one `inputReach` carries. -/
theorem aestronglyMeasurable_reflect_Ioc {u : ℝ → Vec ℝ n} {τ : ℝ}
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 τ))) :
    AEStronglyMeasurable (fun σ => u (τ - σ)) (volume.restrict (Set.Ioc 0 τ)) := by
  have h := aestronglyMeasurable_comp_sub_left (c := τ) hmeas
  rw [sub_zero, sub_self] at h
  exact h.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)

omit [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
set_option maxHeartbeats 400000 in
/-- An admissible input has an integrable solution over its window: bounded by
`U`, and measurable because the exponential factor is continuous. -/
theorem aux_intervalIntegrable_input {A : Mat ℝ n n} {U : S n} {c τ : ℝ} (hτ : 0 ≤ τ)
    (hbdd : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) τ, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 τ))) :
    IntervalIntegrable (fun s => exp ((c - s) • A) *ᵥ u s) volume 0 τ := by
  obtain ⟨CU, hCU⟩ := hbdd.exists_norm_le
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := (0:ℝ)) (b := τ)).exists_bound_of_continuousOn
    (aux_continuous_expSub A c).continuousOn
  have hCE0 : 0 ≤ CE := le_trans (norm_nonneg _) (hCE 0 ⟨le_refl 0, hτ⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ]
  refine ⟨aestronglyMeasurable_mulVec (aux_continuous_expSub A c)
      (hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)),
    HasFiniteIntegral.restrict_of_bounded (C := CE * CU) measure_Ioc_lt_top ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  calc ‖exp ((c - s) • A) *ᵥ u s‖
      ≤ ‖exp ((c - s) • A)‖ * ‖u s‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ CE * CU := mul_le_mul (hCE s ⟨hs.1.le, hs.2⟩)
        (hCU _ (hu s ⟨hs.1.le, hs.2⟩)) (norm_nonneg _) hCE0

/-- Two inputs run back to back: the first over `[0,a]`, the second over the `b`
that follows. Strict `<` so each piece is exact on its own half-open window. -/
noncomputable def aux_concat (u₁ u₂ : ℝ → Vec ℝ n) (a : ℝ) : ℝ → Vec ℝ n :=
  fun s => if a < s then u₂ (s - a) else u₁ s

omit [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
set_option maxHeartbeats 1000000 in
/-- Althoff's Prop. 3.2: what a run over `[0, a+b]` can contribute includes
everything a run over `[0,a]` can contribute, propagated across the remaining
`b`, plus everything a run over `[0,b]` can. -/
theorem LinearSys.inputReach_separation (sys : LinearSys 𝕋 n) {U : S n} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbdd : Bornology.IsBounded (construct U)) :
    (fun y => exp (b • toRealMat sys.A) *ᵥ y) '' sys.inputReach U a + sys.inputReach U b
      ⊆ sys.inputReach U (a + b) := by
  set A := toRealMat sys.A with hA
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]
    exact (exp_add_of_commute hc).symm
  rintro z ⟨w, ⟨y₁, hy₁, rfl⟩, y₂, hy₂, rfl⟩
  obtain ⟨u₁, hu₁mem, hu₁meas, rfl⟩ := hy₁
  obtain ⟨u₂, hu₂mem, hu₂meas, rfl⟩ := hy₂
  have hab : a ≤ a + b := by linarith
  have hu₁int := aux_intervalIntegrable_input (A := A) (c := a) ha hbdd hu₁mem hu₁meas
  have hu₂int := aux_intervalIntegrable_input (A := A) (c := b) hb hbdd hu₂mem hu₂meas
  -- the concatenation is admissible on the joined window
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) (a + b), aux_concat u₁ u₂ a s ∈ construct U := by
    intro s hs
    simp only [aux_concat]
    split_ifs with h
    · exact hu₂mem _ ⟨by linarith, by linarith [hs.2]⟩
    · exact hu₁mem _ ⟨hs.1, not_lt.mp h⟩
  have hmeas : AEStronglyMeasurable (aux_concat u₁ u₂ a)
      (volume.restrict (Set.Icc 0 (a + b))) := by
    have hsplit : Set.Icc (0:ℝ) (a + b) = Set.Icc 0 a ∪ Set.Ioc a (a + b) :=
      (Set.Icc_union_Ioc_eq_Icc ha hab).symm
    have hdisj : Disjoint (Set.Icc (0:ℝ) a) (Set.Ioc a (a + b)) :=
      Set.disjoint_left.mpr fun _ hx hx' => absurd hx.2 (not_le.mpr hx'.1)
    rw [hsplit, Measure.restrict_union hdisj measurableSet_Ioc]
    refine AEStronglyMeasurable.add_measure ?_ ?_
    · refine hu₁meas.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simp only [aux_concat, if_neg (not_lt.mpr hs.2)]
    · have hshift := aestronglyMeasurable_comp_sub_right (c := a) hu₂meas
      rw [zero_add] at hshift
      refine (hshift.mono_measure (Measure.restrict_mono ?_ le_rfl)).congr ?_
      · exact fun s hs => ⟨hs.1.le, by linarith [hs.2]⟩
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        simp only [aux_concat, if_pos hs.1]
  refine ⟨aux_concat u₁ u₂ a, hmem, hmeas, ?_⟩
  -- and what it contributes is the propagated first plus the second
  have hconcat_int : IntervalIntegrable
      (fun s => exp ((a + b - s) • A) *ᵥ aux_concat u₁ u₂ a s) volume 0 (a + b) :=
    aux_intervalIntegrable_input (A := A) (c := a + b) (by linarith) hbdd hmem hmeas
  have hab0 : (0:ℝ) ≤ a + b := by linarith
  have hsub₁ : Set.uIcc (0:ℝ) a ⊆ Set.uIcc (0:ℝ) (a + b) := by
    rw [Set.uIcc_of_le ha, Set.uIcc_of_le hab0]
    exact Set.Icc_subset_Icc le_rfl hab
  have hsub₂ : Set.uIcc a (a + b) ⊆ Set.uIcc (0:ℝ) (a + b) := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hab0]
    exact Set.Icc_subset_Icc ha le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := a) (hconcat_int.mono_set hsub₁) (hconcat_int.mono_set hsub₂)]
  congr 1
  · -- the first window, with the propagator across `b` pulled out
    have hpull : (∫ s in (0:ℝ)..a, exp ((a + b - s) • A) *ᵥ u₁ s)
        = exp (b • A) *ᵥ ∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u₁ s := by
      have hcomm : (∫ s in (0:ℝ)..a, mulVecL (exp (b • A)) (exp ((a - s) • A) *ᵥ u₁ s))
          = exp (b • A) *ᵥ ∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u₁ s :=
        ContinuousLinearMap.intervalIntegral_comp_comm _ hu₁int
      rw [← hcomm]
      refine intervalIntegral.integral_congr fun s _ => ?_
      show exp ((a + b - s) • A) *ᵥ u₁ s = exp (b • A) *ᵥ (exp ((a - s) • A) *ᵥ u₁ s)
      rw [show a + b - s = b + (a - s) from by ring, Matrix.mulVec_mulVec, hmul]
    show exp (b • A) *ᵥ (∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u₁ s) = _
    rw [← hpull]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ha] at hs
    simp only [aux_concat, if_neg (not_lt.mpr hs.2)]
  · -- the second window, shifted back to start at zero
    have hsub := intervalIntegral.integral_comp_sub_right (a := a) (b := a + b)
      (fun σ : ℝ => exp ((b - σ) • A) *ᵥ u₂ σ) a
    rw [sub_self, add_sub_cancel_left] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with s hs
    rw [Set.uIoc_of_le hab] at hs
    simp only [aux_concat, if_pos hs.1]
    have hrw : a + b - s = b - (s - a) := by ring
    rw [hrw]

end CORALean.Real
