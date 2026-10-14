module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.DeltaReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `deltaReachFloat` contains every difference the flow spans over the step

`deltaReach_outer`'s argument at the float matrices:
`e^{As} x - x = (s/Δt)(e^{AΔt} - I) x + (e^{As} - I - (s/Δt)(e^{AΔt} - I)) x`. The
first term is on the segment from the origin to `([e^{AΔt}] - I) R`, once
`e^{AΔt} - I` is in `[e^{AΔt}] - I`; the second is in `[F] R` by
`MatExp.expDiff_mem_intervalCorrectionMatrix`, as in `timeIntervalStepFloat_outer`.
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

/-- The stored negated identity is the point interval at `-1`. -/
theorem aux_negOne_mem_point :
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
theorem aux_zero_mem_origin :
    (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.construct := by
  have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (FloatOps.zero : 𝕋))
  rwa [show RealImage.realImage (fun _ : Fin n => (FloatOps.zero : 𝕋)) = (0 : Vec ℝ n) from
    funext fun _ => toReal_zero] at h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every difference `e^{As} x - x` between a state of the step and the state it
started from, for `x ∈ R` and `s ∈ [0, Δt]`. -/
theorem LinearSys.deltaReachFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) (R : Zonotope (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ R.construct) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ toReal Δt) :
    exp (s • Scalar.toRealMat sys.A) *ᵥ x - x
      ∈ (sys.deltaReachFloat Δt η R).construct := by -- --- PROOF ---
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
