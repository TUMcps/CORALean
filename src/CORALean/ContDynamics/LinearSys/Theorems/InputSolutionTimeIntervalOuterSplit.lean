module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput

@[expose] public section

/-!
# A time-interval input enclosure when the input set misses the origin

Althoff's second case. `inputSolution_timeInterval_outer` needs `0 ∈ U`, and
when that fails the thesis splits the input set into a constant `ũ` and a set
`Ũ` containing the origin, encloses each contribution, and adds them.

`Ũ` goes through Prop. 3.3 unchanged. The constant does not need it: what it
contributes is `∫₀ᵗ e^{Aσ}dσ` applied to it, so the enclosure is the straight
line to its value at `r` widened by the interpolation error — Althoff's
`(t/r)x̃_p(r) ⊕ F̃ũ`, with `F̃` the `constCorrectionMatrix` and no matrix inverse
anywhere.

The two pieces want different sets: `F̃` multiplies a set holding the constant
alone, the propagated part one holding the segment from the origin to it, since
`M` applied to that segment is the range of `(t/r)·M ũ`.

The split itself is a hypothesis — `ContSet` cannot name a centre — so which `c`
and which sets is the representation's business.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] in


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A plain matrix applied to a point of a set lands in the set's image. -/
theorem aux_mtimes_mem {M : Mat ℝ n n} {W : S n} {y : Vec ℝ n} (hy : y ∈ construct W) :
    M *ᵥ y ∈ construct (Mtimes.mtimes M W) := by
  refine Mtimes.mtimes_outer _ _ ?_
  simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
  exact Set.mem_image_of_mem _ hy

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- The same for any matrix an interval matrix denotes. -/
theorem aux_mtimesIM_mem [Mtimes ℐ S]
    {IM : Interval (Mat ℝ n n)} {W : S n}
    {M : Mat ℝ n n} (hM : M ∈ IM.construct) {y : Vec ℝ n} (hy : y ∈ construct W) :
    M *ᵥ y ∈ construct (Mtimes.mtimes (𝕄 := ℐ) IM W) := by
  refine Mtimes.mtimes_outer _ _ ?_
  exact Set.mem_biUnion hM (Set.mem_image_of_mem _ hy)


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- The input's contribution at every time of the step, split along
`U ⊆ {c} ⊕ U₀`. Neither piece needs `0 ∈ U`. -/
theorem LinearSys.CanonicalTrajectory.inputSolution_timeInterval_outer_split
    [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U U₀ P Sg : S n} {x u : ℝ → Vec ℝ n}
    {c : Vec ℝ n} {r : ℝ}
    (traj : sys.CanonicalTrajectory T R₀ U x u) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    -- the split, and the two sets the constant part is enclosed against
    (hsplit : ∀ y ∈ construct U, y - c ∈ construct U₀)
    (hcP : c ∈ construct P)
    (hcS : ∀ lam ∈ Set.Icc (0:ℝ) 1, lam • c ∈ construct Sg)
    (hbddP : Bornology.IsBounded (construct P))
    -- what Prop. 3.3 asks of the part holding the origin
    (h0₀ : (0 : Vec ℝ n) ∈ construct U₀)
    (hconv₀ : Convex ℝ (construct U₀)) (hclosed₀ : IsClosed (construct U₀))
    (hbdd₀ : Bornology.IsBounded (construct U₀))
    (hRconv₀ : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hRclosed₀ : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hRbdd₀ : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U₀)))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    -- the propagated constant, its interpolation error, and the recentred set
    (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (Plus.plus
          (Plus.plus
            (Mtimes.mtimes (𝕄 := Mat ℝ)
              (MatExp.expIntegral (toRealMat sys.A) r) Sg)
            (Mtimes.mtimes (𝕄 := ℐ) (MatExp.constCorrectionMatrix (toRealMat sys.A) r η) P))
          (sys.inputSolution r η U₀)) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  -- the two admissible pieces
  have hmemP : ∀ s ∈ Set.Icc (0:ℝ) t, (fun _ : ℝ => c) s ∈ construct P := fun _ _ => hcP
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, (fun σ => u σ - c) s ∈ construct U₀ :=
    fun s hs => hsplit _ (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun σ => u σ - c)
      (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
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
    · exact aux_mtimes_mem (hcS _ ⟨hs0, hs1⟩)
    · exact aux_mtimesIM_mem
        (MatExp.expIntegralDiff_mem_constCorrectionMatrix A hr η hε ht0 htr) hcP
  · -- the centred part: Prop. 3.3, unchanged
    exact sys.inputReach_subset_inputSolution hr η hε hconv₀ hclosed₀ hbdd₀
      hRconv₀ hRclosed₀ hRbdd₀
      (sys.inputReach_mono hbdd₀ h0₀ ht0 htr ⟨fun σ => u σ - c, hmem₀, hmeas₀, rfl⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
