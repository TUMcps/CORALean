module

public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepZonoFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MatZonoCorrectionMatrixFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.MatSmulOuter

@[expose] public section

/-!
# The float matrix-zonotope step holds the flow of every member at every time

`LinParamSys.timeIntervalStepZono_outer` in `𝕋`: `e^{As} x` splits into a point of
the segment from `x` to `e^{AΔt} x`, which `linComb` holds once `e^{AΔt}` is in the
float exponential of `Δt • [A]` (`matSmul_outer` puts `Δt • A` there), and the
interpolation error, which `F` holds. Both orders' smallness conditions are float
checks on the boxes the zonotopes enclose.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.timeIntervalStepZonoFloat_outer
    (sys : LinParamSys 𝕄𝒵[𝕋] n) {Δt : 𝕋} {m : ℕ}
    (hΔt : 0 < toReal Δt)
    (hεe : toReal (MatExp.normUpperBound (Zonotope.matSmul Δt Δt sys.A).matInterval)
      / (((m + 2 : ℕ) : ℝ) + 2) ≤ 1 / 2)
    (hεF : toReal (MatExp.normUpperBound (Interval.smul Δt Δt sys.A.matInterval))
      / (((m + 2 : ℕ) : ℝ) + 2) ≤ 1 / 2)
    (R : Zonotope (Vec 𝕋 n)) {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) {x : Vec ℝ n}
    (hx : x ∈ R.construct) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ toReal Δt) :
    exp (s • A) *ᵥ x ∈ (sys.timeIntervalStepZonoFloat Δt (m + 2) R).construct := by -- --- PROOF ---
  set r := toReal Δt
  have hl0 : 0 ≤ s / r := div_nonneg hs0 hΔt.le
  have hl1 : s / r ≤ 1 := (div_le_one hΔt).mpr hs
  -- the flow splits into a point of the segment and the interpolation error
  have hdecomp : exp (s • A) *ᵥ x
      = ((1 - s / r) • x + (s / r) • (exp (r • A) *ᵥ x))
        + (exp (s • A) - 1 - (s / r) • (exp (r • A) - 1)) *ᵥ x := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul]
    abel
  -- `Δt • A` lies in the scaled matrix zonotope, so `e^{AΔt} x` in its exponential times `R`
  have hrA : r • A ∈ (Zonotope.matSmul Δt Δt sys.A).construct :=
    Zonotope.matSmul_outer le_rfl le_rfl sys.A hA
  have hE : exp (r • A) *ᵥ x ∈ construct
    (Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋]) (S := 𝒵[𝕋])
      (MatExp.expMatZonoEnclosure (Zonotope.matSmul Δt Δt sys.A) (m + 2)) R) :=
    Mtimes.mtimes_outer (𝕄 := 𝕄𝒵[𝕋])
      (S := 𝒵[𝕋]) _ R
      (Set.mem_biUnion (MatExp.exp_mem_expMatZonoEnclosure _ (m + 2) hrA hεe)
        (Set.mem_image_of_mem _ hx))
  -- the interpolation error lies in `F R`
  have hF : (exp (s • A) - 1 - (s / r) • (exp (r • A) - 1)) *ᵥ x ∈ construct
      (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.matZonoCorrectionMatrix sys.A Δt (m + 2)) R) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R
      (Set.mem_biUnion (MatExp.expDiff_mem_matZonoCorrectionMatrix _ hΔt hεF hA hs0 hs)
        (Set.mem_image_of_mem _ hx))
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add (LinComb.linComb_outer _ _ ?_) hF)
  exact ⟨x, hx, _, hE, 1 - s / r, ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
