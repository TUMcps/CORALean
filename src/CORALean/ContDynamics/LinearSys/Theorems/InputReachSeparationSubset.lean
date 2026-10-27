module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL

@[expose] public section

/-!
# The input reach set comes apart at any intermediate time

[1, Prop. 4] in the direction `InputReachSeparation` leaves open: every run over `[0, a+b]` is its
own first `a` propagated across the remaining `b`, plus its own last `b`. Nothing is built here,
both inputs are the given one read on a different window, so the work is all in the integral.
Splitting at `a` is legal because `intervalIntegrable_expSub_mulVec` holds on the whole window;
`e^{(a+b-s)A} = e^{bA} e^{(a-s)A}` pulls the propagator out of the first piece, and
`integral_comp_add_left` moves the second back to a window starting at zero
(`aux_aestronglyMeasurable_comp_add_left`). With `InputReachSeparationEq` the two inclusions give
the equality [1, Prop. 4] prints.

## Inputs
* `sys` – linear system
* `U` – input set
* `a` – first window length
* `b` – second window length

## Hypotheses
* `ha` – first length nonnegative
* `hb` – second length nonnegative
* `hbdd` – input set bounded

## Conclusion
* the contribution of the joined window lies in the propagated first plus the second

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Translating by `c` carries `Icc (a-c) (b-c)` onto `Icc a b` and preserves
Lebesgue measure. -/
private theorem aux_aestronglyMeasurable_comp_add_left {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) : -- --- CONCL ---
    AEStronglyMeasurable (fun σ => f (c + σ))
      (volume.restrict (Set.Icc (a - c) (b - c))) := by -- --- PROOF ---
  have hpre : (fun σ : ℝ => c + σ) ⁻¹' Set.Icc a b = Set.Icc (a - c) (b - c) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => c + σ)
      (volume.restrict (Set.Icc (a - c) (b - c))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (measurePreserving_add_left volume c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp


-- =======================================  MAIN THEOREM  ======================================= --

-- the given input, read on each half of the window the split produces
/-- [1, Prop. 4]: what a run over `[0, a+b]` contributes is no more than what
some run over `[0,a]` contributes, propagated across the remaining `b`, plus
what some run over `[0,b]` contributes. -/
theorem LinearSys.inputReach_separation_subset (sys : LinearSys 𝕋 n) {U : S n} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbdd : Bornology.IsBounded (construct U)) : -- --- CONCL ---
    sys.inputReach U (a + b)
      ⊆ (fun y => exp (b • toRealMat sys.A) *ᵥ y) '' sys.inputReach U a
        + sys.inputReach U b := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]
    exact (exp_add_of_commute hc).symm
  rintro z ⟨u, humem, humeas, rfl⟩
  rw [← hA]
  have hab : a ≤ a + b := by linarith
  have hab0 : (0:ℝ) ≤ a + b := by linarith
  have huint := intervalIntegrable_expSub_mulVec (A := A) (c := a + b) hab0 hbdd humem humeas
  -- the given input on the first window, which is a subwindow of its own
  have hu₁mem : ∀ s ∈ Set.Icc (0:ℝ) a, u s ∈ construct U :=
    fun s hs => humem s ⟨hs.1, hs.2.trans hab⟩
  have hu₁meas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 a)) :=
    humeas.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl hab) le_rfl)
  have hu₁int := intervalIntegrable_expSub_mulVec (A := A) (c := a) ha hbdd hu₁mem hu₁meas
  -- and on the second, shifted back to a window starting at zero
  have hu₂mem : ∀ t ∈ Set.Icc (0:ℝ) b, u (a + t) ∈ construct U :=
    fun t ht => humem _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hu₂meas : AEStronglyMeasurable (fun t => u (a + t))
      (volume.restrict (Set.Icc 0 b)) := by
    have hshift := aux_aestronglyMeasurable_comp_add_left (c := a) humeas
    rw [zero_sub, add_sub_cancel_left] at hshift
    exact hshift.mono_measure
      (Measure.restrict_mono (Set.Icc_subset_Icc (by linarith) le_rfl) le_rfl)
  -- the first window, with the propagator across `b` pulled out
  have hpull : (∫ s in (0:ℝ)..a, exp ((a + b - s) • A) *ᵥ u s)
      = exp (b • A) *ᵥ ∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u s := by
    have hcomm : (∫ s in (0:ℝ)..a, mulVecL (exp (b • A)) (exp ((a - s) • A) *ᵥ u s))
        = exp (b • A) *ᵥ ∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u s :=
      ContinuousLinearMap.intervalIntegral_comp_comm _ hu₁int
    rw [← hcomm]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show exp ((a + b - s) • A) *ᵥ u s = exp (b • A) *ᵥ (exp ((a - s) • A) *ᵥ u s)
    rw [show a + b - s = b + (a - s) from by ring, Matrix.mulVec_mulVec, hmul]
  -- the second window, shifted back to start at zero
  have hshiftint : (∫ s in a..(a + b), exp ((a + b - s) • A) *ᵥ u s)
      = ∫ t in (0:ℝ)..b, exp ((b - t) • A) *ᵥ u (a + t) := by
    have hcomp := intervalIntegral.integral_comp_add_left
      (a := (0:ℝ)) (b := b) (fun σ : ℝ => exp ((a + b - σ) • A) *ᵥ u σ) a
    rw [add_zero] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show exp ((a + b - (a + t)) • A) *ᵥ u (a + t) = exp ((b - t) • A) *ᵥ u (a + t)
    rw [show a + b - (a + t) = b - t from by ring]
  -- the split itself, legal because the whole window is integrable
  have hsub₁ : Set.uIcc (0:ℝ) a ⊆ Set.uIcc (0:ℝ) (a + b) := by
    rw [Set.uIcc_of_le ha, Set.uIcc_of_le hab0]
    exact Set.Icc_subset_Icc le_rfl hab
  have hsub₂ : Set.uIcc a (a + b) ⊆ Set.uIcc (0:ℝ) (a + b) := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hab0]
    exact Set.Icc_subset_Icc ha le_rfl
  have hsplit : (∫ s in (0:ℝ)..(a + b), exp ((a + b - s) • A) *ᵥ u s)
      = exp (b • A) *ᵥ (∫ s in (0:ℝ)..a, exp ((a - s) • A) *ᵥ u s)
        + ∫ t in (0:ℝ)..b, exp ((b - t) • A) *ᵥ u (a + t) := by
    rw [← hpull, ← hshiftint]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (huint.mono_set hsub₁) (huint.mono_set hsub₂)).symm
  rw [hsplit]
  exact Set.add_mem_add (Set.mem_image_of_mem _ ⟨u, hu₁mem, hu₁meas, rfl⟩)
    ⟨fun t => u (a + t), hu₂mem, hu₂meas, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
