module

public import CORALean.ContDynamics.LinearSys.Operations.PostDeltaFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachRecenter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `postDeltaFloat` holds every difference a run spans over the step

A run of `ẋ = Ax + u`, `u(t) ∈ V`, splits at time `t` into the free motion's
difference `e^{At} x(0) - x(0)`, the constant `ũ`'s share `∫₀ᵗ e^{Aσ}dσ ũ`, and the
rest, which `sub_mem_inputReach_recenter` places in `Ũ`'s input reach at `t`. Each
lies in its summand: `aux_deltaReachFloat_outer`, and the two input reaches at `t`
inside those at `Δt` (`inputReach_mono`, both sets holding `0`), which
`inputSolutionFloat` encloses.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `R` – float start zonotope
* `V` – input float zonotope
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `t` – time

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `traj` – signal is a canonical trajectory
* `hUV` – input set lies in the float zonotope
* `ht` – time within the step

## Conclusion
* the state difference lies in the float post-delta zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The stored negated identity is the point interval at `-1`. -/
private theorem aux_negOne_mem_point : -- --- CONCL ---
    (-1 : Mat ℝ n n) ∈ (Interval.point (negIdentityMat 𝕋 n)).construct := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 n n) (negIdentityMat 𝕋 n)
  have he : (RealImage.realImage (α := Mat 𝕋 n n) (negIdentityMat 𝕋 n) : Mat ℝ n n) = -1 := by
    funext i j
    show toReal (if i = j then FloatOps.neg (FloatOps.one : 𝕋) else FloatOps.zero)
      = (-1 : Mat ℝ n n) i j
    by_cases hij : i = j
    · rw [if_pos hij, toReal_neg, toReal_one, hij]; simp
    · rw [if_neg hij, toReal_zero]; simp [Matrix.one_apply_ne hij]
  rwa [he] at h


/-- The origin's generator-free zonotope holds `0`. -/
private theorem aux_zero_mem_origin :
    (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.construct := by
  have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (FloatOps.zero : 𝕋))
  rwa [show RealImage.realImage (fun _ : Fin n => (FloatOps.zero : 𝕋)) = (0 : Vec ℝ n) from
    funext fun _ => toReal_zero] at h0


/-- Every difference `e^{As} x - x` between a state of the step and the state it
started from, for `x ∈ R` and `s ∈ [0, Δt]`. -/
private theorem LinearSys.aux_deltaReachFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η) (R : Zonotope (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ R.construct) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ toReal Δt) : -- --- CONCL ---
    exp (s • Scalar.toRealMat sys.A) *ᵥ x - x
      ∈ (sys.step_deltaReachFloat Δt η R).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
  set A := Scalar.toRealMat sys.A
  set r := toReal Δt
  have hl0 : 0 ≤ s / r := div_nonneg hs0 hΔt.le
  have hl1 : s / r ≤ 1 := (div_le_one hΔt).mpr hs
  -- the difference splits into a point of the segment from `0` and the interpolation error
  have hdecomp : exp (s • A) *ᵥ x - x
      = (s / r) • ((exp (r • A) - 1) *ᵥ x)
        + (exp (s • A) - 1 - (s / r) • (exp (r • A) - 1)) *ᵥ x := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, smul_sub]
    abel
  -- `(e^{AΔt} - I) x` lies in `([e^{AΔt}] - I) R`
  have hE : (exp (r • A) - 1) *ᵥ x ∈ construct (Mtimes.mtimes (S := 𝒵[𝕋])
      (𝕄 := ℐ[𝕋]) (Interval.matPlus (sys.expIntervalFloat Δt Δt (m + 2))
        (Interval.point (negIdentityMat 𝕋 n))) R) := by
    have hM := Interval.matPlus_outer _ _ (sys.exp_mem_expIntervalFloat hη le_rfl le_rfl)
      aux_negOne_mem_point
    rw [← sub_eq_add_neg] at hM
    exact Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R
      (Set.mem_biUnion hM (Set.mem_image_of_mem _ hx))
  -- the interpolation error lies in `[F] R`
  have hF : (exp (s • A) - 1 - (s / r) • (exp (r • A) - 1)) *ᵥ x ∈ construct
      (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt (m + 2)) R) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R
      (Set.mem_biUnion (MatExp.expDiff_mem_intervalCorrectionMatrix _ hΔt hη.2
        (Interval.mem_point sys.A) hs0 hs) (Set.mem_image_of_mem _ hx))
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add (LinComb.linComb_outer _ _ ?_) hF)
  exact ⟨0, aux_zero_mem_origin, _, hE, 1 - s / r, ⟨by linarith, by linarith⟩, by
    rw [smul_zero, zero_add, sub_sub_cancel]⟩

end


/-- The generator-free zonotope at the stored zero holds `0`. -/
private theorem aux_zero_mem_segStart :
    (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.construct := by
  have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (FloatOps.zero : 𝕋))
  rwa [show RealImage.realImage (fun _ : Fin n => (FloatOps.zero : 𝕋)) = (0 : Vec ℝ n) from
    funext fun _ => toReal_zero] at h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, Δt]` from `R` under inputs in `U ⊆ V` differs from its start,
at every time of the step, by a point of `postDeltaFloat`. -/
theorem LinearSys.IsCanonicalTrajectory.postDeltaFloat_outer {sys : LinearSys 𝕋 n} {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η) {R V : Zonotope (Vec 𝕋 n)}
    {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 (toReal Δt)) R.construct U
      x u) (hUV : U ⊆ V.construct) {t : ℝ} (ht : t ∈ Set.Icc 0 (toReal Δt)) : -- --- CONCL ---
    x t - x 0 ∈ (sys.postDeltaFloat Δt η R V).construct := by -- --- PROOF ---
  set A := Scalar.toRealMat sys.A with hA
  set ũ := Recenter.center V with hũ
  -- `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  have h0seg : (0 : Vec ℝ n) ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, aux_zero_mem_segStart, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, aux_zero_mem_segStart, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant's share by `t`, inside `P̃^R([0, ũ])`
  have hconst : Real.MatExp.expIntegral A t *ᵥ ũ ∈ (sys.inputSolutionFloat Δt η seg).construct :=
    sys.inputReach_subset_inputSolutionFloat hΔt hη seg
      (sys.inputReach_mono (CompactSet.isBounded_construct seg) h0seg ht.1 ht.2
        ⟨fun _ => ũ, fun _ _ => hũseg, MeasureTheory.aestronglyMeasurable_const,
          (Real.MatExp.expIntegral_constInput A ũ ht.1).symm⟩)
  -- the rest of the input's share by `t`, inside `P^R(Ũ)`
  have hrest := sys.inputReach_subset_inputSolutionFloat hΔt hη _
    (sys.inputReach_mono (CompactSet.isBounded_construct _) (Recenter.zero_mem_recenter V) ht.1
      ht.2 (traj.sub_mem_inputReach_recenter hUV ht))
  -- the free motion's difference, inside `step_deltaReachFloat`
  have hhom := sys.aux_deltaReachFloat_outer hΔt hη R traj.init ht.1 ht.2
  have hsplit : x t - x 0 = (exp (t • A) *ᵥ x 0 - x 0) + (Real.MatExp.expIntegral A t *ᵥ ũ
      + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ))) := by abel
  rw [hsplit]
  exact Plus.plus_outer (sys.step_deltaReachFloat Δt η R) (sys.inputSolutionFloat Δt η seg ⊞
    sys.inputSolutionFloat Δt η (Recenter.recenter V)) (Set.add_mem_add hhom
      (Plus.plus_outer (sys.inputSolutionFloat Δt η seg)
        (sys.inputSolutionFloat Δt η (Recenter.recenter V)) (Set.add_mem_add hconst hrest)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
