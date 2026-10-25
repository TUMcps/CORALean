module

public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat

@[expose] public section

/-!
# The float step holds the flow of every member at every time of the step

`LinearSys.timeIntervalFloat_outer` with a member `A ∈ sys.A` in place of
the stored matrix: `e^{As} x` splits into a point of the segment from `x` to
`e^{AΔt} x`, which `linComb` holds once `e^{AΔt}` is in the float box, and the
interpolation error, which `[F]` at `sys.A` holds.

## Inputs
* `sys` – system
* `Δt` – step size
* `η` – Taylor order
* `R` – initial zonotope
* `A` – system matrix member
* `x` – start point
* `s` – time

## Hypotheses
* `hΔt` – step positive
* `hη` – order admissible
* `hA` – `A` lies in the matrix set
* `hx` – `x` lies in `R`
* `hs0` – time nonnegative
* `hs` – time at most the step

## Conclusion
* the member's flow of the point lies in the float step
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.timeIntervalFloat_outer
    (sys : LinParamSys ℐ[𝕋] n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η) (R : Zonotope (Vec 𝕋 n))
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) {x : Vec ℝ n} (hx : x ∈ R.construct) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ toReal Δt) : -- --- CONCL ---
    exp (s • A) *ᵥ x ∈ (sys.timeIntervalFloat Δt η R).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
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
      (Set.mem_biUnion (sys.exp_mem_expIntervalFloat hη hA le_rfl le_rfl)
        (Set.mem_image_of_mem _ hx))
  -- the interpolation error lies in `[F] R`
  have hF : (exp (s • A) - 1 - (s / r) • (exp (r • A) - 1)) *ᵥ x ∈ construct
      (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalCorrectionMatrix sys.A Δt (m + 2)) R) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R
      (Set.mem_biUnion (MatExp.expDiff_mem_intervalCorrectionMatrix _ hΔt hη.2 hA hs0 hs)
        (Set.mem_image_of_mem _ hx))
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add (LinComb.linComb_outer _ _ ?_) hF)
  exact ⟨x, hx, _, hE, 1 - s / r, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
