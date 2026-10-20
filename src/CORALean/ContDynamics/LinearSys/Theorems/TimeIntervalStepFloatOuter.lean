module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `timeIntervalStepFloat` contains the flow at every time of the step

The argument of `timeIntervalStep_outer_setLinComb`, at the float matrices:
`e^{As} x = ((1 - s/Δt) x + (s/Δt) e^{AΔt} x) + (e^{As} - I - (s/Δt)(e^{AΔt} - I)) x`.
The first term is on the segment `linComb` covers, once `e^{AΔt}` is in
`expIntervalFloat`; the second is in `[F] R` by
`MatExp.expDiff_mem_intervalCorrectionMatrix`, whose norm bound is the one
`OrderAdmissibleFloat` asks of `[Δt, Δt] · A`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `R` – float state zonotope
* `x` – state point
* `s` – time

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `hx` – point lies in the zonotope
* `hs0` – time nonnegative
* `hs` – time within the step

## Conclusion
* the exponential image of the point lies in the float step set
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.timeIntervalStepFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) (R : Zonotope (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ R.construct) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ toReal Δt) : -- --- CONCL ---
    exp (s • Scalar.toRealMat sys.A) *ᵥ x
      ∈ (sys.timeIntervalStepFloat Δt η R).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
  set A := Scalar.toRealMat sys.A
  set r := toReal Δt
  have hl0 : 0 ≤ s / r := div_nonneg hs0 hΔt.le
  have hl1 : s / r ≤ 1 := (div_le_one hΔt).mpr hs
  -- the flow splits into a point of the segment and the interpolation error
  have hdecomp : exp (s • A) *ᵥ x
      = ((1 - s / r) • x + (s / r) • (exp (r • A) *ᵥ x))
        + (exp (s • A) - 1 - (s / r) • (exp (r • A) - 1)) *ᵥ x := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul]
    abel
  -- `e^{AΔt} x` lies in `[e^{AΔt}] R`
  have hE : exp (r • A) *ᵥ x ∈ construct
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (sys.expIntervalFloat Δt Δt (m + 2)) R) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R
      (Set.mem_biUnion (sys.exp_mem_expIntervalFloat hη le_rfl le_rfl)
        (Set.mem_image_of_mem _ hx))
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
  exact ⟨x, hx, _, hE, 1 - s / r, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
