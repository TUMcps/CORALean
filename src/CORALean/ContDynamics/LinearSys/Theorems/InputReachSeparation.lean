import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# The input reach set splits at any intermediate time

[1, Prop. 3.2], in the direction the enclosures need: concatenating an input over
`[0,a]` with one over `[0,b]` gives an input over `[0,a+b]`, and what it
contributes is `e^{Ab}` applied to the first contribution plus the second.

This is the direction that has to build an input rather than take one apart;
`InputReachSeparationSubset` takes one apart, and `InputReachSeparationEq` puts
the two together into the equality [1] prints. Taking `a = Δt` and `b = r` is
[1, Cor. 3.1], which the two-argument form already covers.

The concatenation is measured by splitting the window and rebuilding it:
`intervalIntegrable_expSub_mulVec` gives integrability on each half, and
`aux_aestronglyMeasurable_comp_sub_right` moves the second half's measurability
back to a window starting at zero.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Translating by `c` carries `Icc a b` onto `Icc (a+c) (b+c)` and preserves
Lebesgue measure. -/
theorem aux_aestronglyMeasurable_comp_sub_right {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun σ => f (σ - c))
      (volume.restrict (Set.Icc (a + c) (b + c))) := by -- --- PROOF ---
  have hpre : (fun σ : ℝ => σ - c) ⁻¹' Set.Icc a b = Set.Icc (a + c) (b + c) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => σ - c)
      (volume.restrict (Set.Icc (a + c) (b + c))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (measurePreserving_sub_right volume c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp

/-- Two inputs run back to back: the first over `[0,a]`, the second over the `b`
that follows. Strict `<` so each piece is exact on its own half-open window. -/
noncomputable def aux_concat (u₁ u₂ : ℝ → Vec ℝ n) (a : ℝ) : ℝ → Vec ℝ n :=
  fun s => if a < s then u₂ (s - a) else u₁ s

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in


-- =======================================  MAIN THEOREM  ======================================= --

-- the concatenated input is measured by splitting the window and rebuilding it
set_option maxHeartbeats 1000000 in
/-- [1, Prop. 3.2]: what a run over `[0, a+b]` can contribute includes everything
a run over `[0,a]` can contribute, propagated across the remaining `b`, plus
everything a run over `[0,b]` can. -/
theorem LinearSys.inputReach_separation (sys : LinearSys 𝕋 n) {U : S n} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbdd : Bornology.IsBounded (construct U)) :
    (fun y => exp (b • toRealMat sys.A) *ᵥ y) '' sys.inputReach U a + sys.inputReach U b
      ⊆ sys.inputReach U (a + b) := by -- --- PROOF ---
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
  have hu₁int := intervalIntegrable_expSub_mulVec (A := A) (c := a) ha hbdd hu₁mem hu₁meas
  have hu₂int := intervalIntegrable_expSub_mulVec (A := A) (c := b) hb hbdd hu₂mem hu₂meas
  -- the concatenation is admissible on the joined window
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) (a + b), aux_concat u₁ u₂ a s ∈ construct U := by
    intro s hs
    simp only [aux_concat]
    split_ifs with h
    · exact hu₂mem _ ⟨by linarith, by linarith [hs.2]⟩
    · exact hu₁mem _ ⟨hs.1, not_lt.mp h⟩
  -- measurable on each half of the split window, and the two halves are disjoint
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
    · have hshift := aux_aestronglyMeasurable_comp_sub_right (c := a) hu₂meas
      rw [zero_add] at hshift
      refine (hshift.mono_measure (Measure.restrict_mono ?_ le_rfl)).congr ?_
      · exact fun s hs => ⟨hs.1.le, by linarith [hs.2]⟩
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        simp only [aux_concat, if_pos hs.1]
  refine ⟨aux_concat u₁ u₂ a, hmem, hmeas, ?_⟩
  -- and what it contributes is the propagated first plus the second
  have hconcat_int : IntervalIntegrable
      (fun s => exp ((a + b - s) • A) *ᵥ aux_concat u₁ u₂ a s) volume 0 (a + b) :=
    intervalIntegrable_expSub_mulVec (A := A) (c := a + b) (by linarith) hbdd hmem hmeas
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
