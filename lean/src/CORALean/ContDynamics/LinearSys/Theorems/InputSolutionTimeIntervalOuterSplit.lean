import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec

/-!
# A time-interval input enclosure when the input set misses the origin

Althoff's second case. `inputSolution_timeInterval_outer` needs `0 ∈ U`, and
when that fails the thesis splits the input set into a constant `ũ` and a set
`Ũ` containing the origin, encloses each contribution, and adds them.

`Ũ` goes through Prop. 3.3 unchanged. The constant does not need it: what it
contributes is known in closed form, `∫₀ᵗ e^{Aσ}dσ` applied to it, so the
enclosure is the straight line to its value at `r` widened by the interpolation
error — Althoff's `(t/r)x̃_p(r) ⊕ F̃ũ`, with `F̃` the `constCorrectionMatrix` and
no matrix inverse anywhere.

The two pieces want different sets. `F̃` multiplies a set holding the constant
alone, since the constant is what it corrects; the propagated part multiplies a
set holding the segment from the origin to it, since `M` applied to that segment
is exactly the range of `(t/r)·M ũ`. Splitting them this way is what keeps the
result as tight as the thesis rather than allowing every input in a segment at
every time.

The split itself is a hypothesis: `ContSet` cannot name a centre, so which `c`
and which sets is the representation's business. A zonotope has all three.
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
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OuterContSet S ℝ]

/-- A plain matrix applied to a point of a set lands in the set's image. -/
theorem aux_mtimes_mem {M : Mat ℝ n n} {W : S n} {y : Vec ℝ n} (hy : y ∈ construct W) :
    M *ᵥ y ∈ construct (Mtimes.mtimes M W) := by
  refine Mtimes.mtimes_outer _ _ ?_
  simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
  exact Set.mem_image_of_mem _ hy

omit [OuterContSet S ℝ] in
/-- The same for any matrix an interval matrix denotes. -/
theorem aux_mtimesIM_mem [Mtimes IntervalMat S] {IM : IntervalMat n n} {W : S n}
    {M : Mat ℝ n n} (hM : M ∈ IM.construct) {y : Vec ℝ n} (hy : y ∈ construct W) :
    M *ᵥ y ∈ construct (Mtimes.mtimes IM W) := by
  refine Mtimes.mtimes_outer _ _ ?_
  simp only [IntervalMat.construct_eq]
  exact Set.mem_biUnion hM (Set.mem_image_of_mem _ hy)

set_option maxHeartbeats 400000 in
/-- What a constant input contributes over `[0,t]`, in closed form. The
substitution `σ = t - s` turns the propagator into the integrated exponential. -/
theorem aux_const_integral (A : Mat ℝ n n) (c : Vec ℝ n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ c) = IntervalMat.expIntegral A t *ᵥ c := by
  rw [IntervalMat.expIntegral_mulVec A c ht]
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t)
    (fun σ : ℝ => exp (σ • A) *ᵥ c) t
  simpa using h

set_option maxHeartbeats 1000000 in
/-- The input's contribution at every time of the step, split along
`U ⊆ {c} ⊕ U₀`. Neither piece needs `0 ∈ U`. -/
theorem LinearSys.Trajectory.inputSolution_timeInterval_outer_split [Mtimes IntervalMat S]
    {sys : LinearSys 𝕋 n} {R₀ U U₀ P Sg : S n} {x u : ℝ → Vec ℝ n} {c : Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) (η : ℕ)
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
    (hRconv₀ : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hRclosed₀ : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hRbdd₀ : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₀)))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (OuterContSet.plus
          (OuterContSet.plus
            (Mtimes.mtimes (IntervalMat.expIntegral (toRealMat sys.A) r) Sg)
            (Mtimes.mtimes (IntervalMat.constCorrectionMatrix (toRealMat sys.A) r η) P))
          (sys.inputSolution r η U₀)) := by
  set A := toRealMat sys.A with hA
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  -- the two admissible pieces
  have hmemP : ∀ s ∈ Set.Icc (0:ℝ) t, (fun _ : ℝ => c) s ∈ construct P := fun _ _ => hcP
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, (fun σ => u σ - c) s ∈ construct U₀ :=
    fun s hs => hsplit _ (traj.input s hs.1)
  have hmeas₀ : AEStronglyMeasurable (fun σ => u σ - c)
      (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input le_rfl).sub aestronglyMeasurable_const
  have hint₁ := aux_intervalIntegrable_input (A := A) (c := t) ht0 hbddP hmemP
    aestronglyMeasurable_const
  have hint₀ := aux_intervalIntegrable_input (A := A) (c := t) ht0 hbdd₀ hmem₀ hmeas₀
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
  refine OuterContSet.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the constant part: the straight line, widened by the interpolation error
    rw [aux_const_integral A c ht0]
    have hdecomp : IntervalMat.expIntegral A t *ᵥ c
        = (IntervalMat.expIntegral A r *ᵥ ((t / r) • c))
          + (IntervalMat.expIntegral A t - (t / r) • IntervalMat.expIntegral A r) *ᵥ c := by
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec]
      abel
    rw [hdecomp]
    refine OuterContSet.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · exact aux_mtimes_mem (hcS _ ⟨hs0, hs1⟩)
    · exact aux_mtimesIM_mem
        (IntervalMat.expIntegralDiff_mem_constCorrectionMatrix A hr η hε ht0 htr) hcP
  · -- the centred part: Prop. 3.3, unchanged
    exact sys.inputReach_subset_inputSolution hr η hε hconv₀ hclosed₀ hbdd₀
      hRconv₀ hRclosed₀ hRbdd₀
      (sys.inputReach_mono hbdd₀ h0₀ ht0 htr ⟨fun σ => u σ - c, hmem₀, hmeas₀, rfl⟩)

end CORALean.Real
