module

public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepZono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MatZonoCorrectionMatrix
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The step at a matrix zonotope holds every member's flow at every time of the step

`LinParamSys.timeIntervalStep_outer` at `𝕄𝒵`: `e^{tA} x₀` splits into a point of
the segment from `x₀` to `e^{rA} x₀`, which `linComb` holds once `e^{rA}` is in the
matrix-zonotope exponential of `r • A` (`exp_mem_expMatZonoEnclosure`, `r • A` a
member of the scaled zonotope), and the interpolation error, which the
matrix-zonotope correction matrix holds (`expDiff_mem_matZonoCorrectionMatrix`).
Two conditions, one per enclosure, each checkable from `sys.A` alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes 𝕄𝒵 S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow of every member of the matrix
zonotope, at every time of the step. -/
theorem LinParamSys.timeIntervalStepZono_outer (sys : LinParamSys 𝕄𝒵 n) {r : ℝ} (hr : 0 < r)
    {m : ℕ}
    (hεe : ‖(Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) r) sys.A).interval.absMax‖
      / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hεF : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (X₀ : S n) {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (fun x₀ => exp (t • A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timeIntervalStepZono r (m + 2) X₀) := by -- --- PROOF ---
  rintro y ⟨x₀, hx₀, rfl⟩
  -- the flow is the straight line plus what the curvature adds
  have hdecomp : exp (t • A) *ᵥ x₀
      = ((1 - t / r) • x₀ + (t / r) • (exp (r • A) *ᵥ x₀))
        + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x₀ := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul]
    abel
  have hrA : r • A ∈ (Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) r) sys.A).construct := by
    rw [← Zonotope.map_exact]
    exact ⟨A, hA, by simp⟩
  show exp (t • A) *ᵥ x₀ ∈ _
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the endpoint is the matrix-zonotope exponential of `r • A`
    refine LinComb.linComb_outer _ _ ⟨x₀, hx₀, exp (r • A) *ᵥ x₀, ?_, 1 - t / r, ?_, ?_⟩
    · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
        (MatExp.exp_mem_expMatZonoEnclosure _ (m + 2) hrA hεe)
        (Set.mem_image_of_mem _ hx₀))
    · exact ⟨by linarith [div_le_one_of_le₀ htr hr.le], by linarith [div_nonneg ht0 hr.le]⟩
    · rw [sub_sub_cancel]
  · -- and the curvature term is the correction matrix acting on `X₀`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expDiff_mem_matZonoCorrectionMatrix sys.A hr hεF hA ht0 htr)
      (Set.mem_image_of_mem _ hx₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
