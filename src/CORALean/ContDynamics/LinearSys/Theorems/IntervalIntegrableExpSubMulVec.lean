module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# An admissible input against the exponential is interval integrable

`Matrix` is a plain `def`, so instance search finds no metrizable structure on
it and a matrix-valued factor never gets `Continuous.aestronglyMeasurable`;
`aux_aestronglyMeasurable_mulVec` goes one entry at a time instead. The bound
is built from two `exists_bound` witnesses: one for the input set, one for the
exponential over the compact step. `InputReachSeparation` needs this three
times over, at the three windows a concatenation splits into.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A continuous matrix applied to a measurable vector, entry by entry. -/
theorem aux_aestronglyMeasurable_mulVec {M : ℝ → Mat ℝ n n} {v : ℝ → Vec ℝ n} {μ : Measure ℝ}
    (hM : Continuous M) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun s => M s *ᵥ v s) μ := by -- --- PROOF ---
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

/-- The integrand of an input solution is continuous in its matrix factor. -/
theorem aux_continuous_expSub (A : Mat ℝ n n) (c : ℝ) :
    Continuous fun s : ℝ => exp ((c - s) • A) :=
  exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)


-- =======================================  MAIN THEOREM  ======================================= --

/-- An admissible input has an integrable solution over its window: bounded by
`U`, and measurable because the exponential factor is continuous. -/
theorem intervalIntegrable_expSub_mulVec {A : Mat ℝ n n} {U : S n} {c τ : ℝ} (hτ : 0 ≤ τ)
    (hbdd : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) τ, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 τ))) : -- --- CONCL ---
    IntervalIntegrable (fun s => exp ((c - s) • A) *ᵥ u s) volume 0 τ := by -- --- PROOF ---
  obtain ⟨CU, hCU⟩ := hbdd.exists_norm_le
  obtain ⟨CE, hCE⟩ := (isCompact_Icc (a := (0:ℝ)) (b := τ)).exists_bound_of_continuousOn
    (aux_continuous_expSub A c).continuousOn
  have hCE0 : 0 ≤ CE := le_trans (norm_nonneg _) (hCE 0 ⟨le_refl 0, hτ⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ]
  refine ⟨aux_aestronglyMeasurable_mulVec (aux_continuous_expSub A c)
      (hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)),
    HasFiniteIntegral.restrict_of_bounded (C := CE * CU) measure_Ioc_lt_top ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  calc ‖exp ((c - s) • A) *ᵥ u s‖
      ≤ ‖exp ((c - s) • A)‖ * ‖u s‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ CE * CU := mul_le_mul (hCE s ⟨hs.1.le, hs.2⟩)
        (hCU _ (hu s ⟨hs.1.le, hs.2⟩)) (norm_nonneg _) hCE0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
