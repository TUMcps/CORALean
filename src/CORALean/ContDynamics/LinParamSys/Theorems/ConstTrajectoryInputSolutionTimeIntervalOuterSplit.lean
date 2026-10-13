module

public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec

@[expose] public section

/-!
# A time-interval input enclosure at a box, when the input set misses the origin

`inputSolution_timeInterval_outer` needs `0 ∈ U`; this is [1, Alg. 4]'s second
case, the input set split into a constant `ũ` and a set `Ũ` holding the origin.
`Ũ` goes through Prop. 3.3 unchanged, and the constant contributes
`(∫₀ᵗ e^{Aσ}dσ)ũ`, enclosed as the straight line to its value at `r` widened by
`intervalConstCorrectionMatrix`, Althoff's `F̃` over the whole box.

The propagated half differs from the point case, and this is where the matrix
being a set is paid for: there the line is `expIntegral A r` applied to the
segment, an exact matrix no machine holds. Here `A` is a box, so the same
`C(r) := ∫₀ʳ e^{At}dt` of [1, Alg. 4] is the series `inputSolution` already
encloses — applied to the segment rather than to an input set. Distributing the
product over that sum is the tightness this costs.

The split itself is a hypothesis, `ContSet` being unable to name a centre.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

-- a three-way `plus` in the conclusion, every factor an interval matrix at `ℐ`
/-- The input's contribution at every time of the step, split along
`U ⊆ {c} ⊞ U₀`. Neither piece needs `0 ∈ U`. -/
theorem LinParamSys.ConstTrajectory.inputSolution_timeInterval_outer_split
    {sys : LinParamSys ℐ n} {T : Set ℝ} {R₀ U U₀ P Sg : S n} {x u : ℝ → Vec ℝ n}
    {A : Mat ℝ n n} {c : Vec ℝ n} {r : ℝ}
    (traj : sys.ConstTrajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    -- the split, then the segment, the constant, and the part holding the origin
    (hsplit : ∀ y ∈ construct U, y - c ∈ construct U₀) (hcP : c ∈ construct P)
    (hcS : ∀ lam ∈ Set.Icc (0:ℝ) 1, lam • c ∈ construct Sg)
    (hbddP : Bornology.IsBounded (construct P))
    (hconvS : Convex ℝ (construct Sg)) (hclosedS : IsClosed (construct Sg))
    (hbddS : Bornology.IsBounded (construct Sg))
    (hRconvS : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) Sg)))
    (hRclosedS : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) Sg)))
    (hRbddS : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) Sg)))
    (h0₀ : (0 : Vec ℝ n) ∈ construct U₀) (hconv₀ : Convex ℝ (construct U₀))
    (hclosed₀ : IsClosed (construct U₀)) (hbdd₀ : Bornology.IsBounded (construct U₀))
    (hRconv₀ : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U₀)))
    (hRclosed₀ : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U₀)))
    (hRbdd₀ : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U₀)))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s) ∈ construct (Plus.plus (Plus.plus
      (sys.inputSolution r η Sg) (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalConstCorrectionMatrix sys.A r η) P))
      (sys.inputSolution r η U₀)) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  -- the fixed member names the point system the closed form is read at
  have lin := traj.toLinearSys
  have hmemP : ∀ s ∈ Set.Icc (0:ℝ) t, (fun _ : ℝ => c) s ∈ construct P := fun _ _ => hcP
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, (fun σ => u σ - c) s ∈ construct U₀ :=
    fun s hs => hsplit _ (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun σ => u σ - c)
      (volume.restrict (Set.Icc 0 t)) :=
    (lin.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht0 hbddP hmemP
    aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht0 hbdd₀ hmem₀ hmeas₀
  -- linearity splits the integral along the split of `U`
  have hsum : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      = (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ c)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - c) := by
    rw [← intervalIntegral.integral_add hint₁ hint₀]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  rw [hsum]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the constant part: the straight line, widened by the interpolation error
    rw [MatExp.expIntegral_constInput A c ht0]
    have hdecomp : MatExp.expIntegral A t *ᵥ c
        = (MatExp.expIntegral A r *ᵥ ((t / r) • c))
          + (MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r) *ᵥ c := by
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec]
      abel
    rw [hdecomp]
    refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · -- `C(r)` applied to the segment is a constant input's own `inputSolution`
      have hline := sys.inputSolution_outer hr η hε traj.param hconvS hclosedS hbddS
        hRconvS hRclosedS hRbddS (u := fun _ : ℝ => (t / r) • c)
        (fun _ _ => hcS _ ⟨hs0, hs1⟩) aestronglyMeasurable_const
      rwa [MatExp.expIntegral_constInput A ((t / r) • c) hr.le] at hline
    · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
        (MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix sys.A hr η hε
          traj.param ht0 htr)
        (Set.mem_image_of_mem _ hcP))
  · -- the centred part: Prop. 3.3 at the member, unchanged
    exact sys.inputReach_subset_inputSolution hr η hε traj.param hconv₀ hclosed₀ hbdd₀
      hRconv₀ hRclosed₀ hRbdd₀
      ((LinearSys.mk A : LinearSys ℝ n).inputReach_mono hbdd₀ h0₀ ht0 htr
        ⟨fun σ => u σ - c, hmem₀, hmeas₀, by simp only [Scalar.toRealMat_real]⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
