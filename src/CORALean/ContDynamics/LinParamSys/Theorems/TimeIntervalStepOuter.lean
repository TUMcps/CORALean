module

public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrix
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# `timeIntervalStep` contains the flow of every matrix the set holds

`LinearSys.timeIntervalStep_outer_at` at a matrix drawn from `construct sys.A`
instead of the one a point system stores: the straight line from `X₀` to its
image is a `linComb` at weight `1 - t/r` as before, and the interpolation error
is what the box's correction matrix spans.

The image is taken at `e^{tA}` for one member `A`, which is `'constParam'`: the
same matrix at every instant of the step. A time-varying reading needs
`e^{tA(t)}`, which is not a matrix exponential of anything, and the argument
below does not reach it.

Homogeneous only, as in the point case.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
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
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow of every member, at every time
of the step. -/
theorem LinParamSys.timeIntervalStep_outer (sys : LinParamSys ℐ n) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (X₀ : S n) {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- STMT ---
    (fun x₀ => exp (t • A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timeIntervalStep r (m + 2) X₀) := by -- --- PROOF ---
  rintro y ⟨x₀, hx₀, rfl⟩
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  -- the flow is the straight line plus what the curvature adds
  have hdecomp : exp (t • A) *ᵥ x₀
      = ((1 - t / r) • x₀ + (t / r) • (exp (r • A) *ᵥ x₀))
        + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x₀ := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul]
    abel
  show exp (t • A) *ᵥ x₀ ∈ _
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the endpoint is the exponential of the scaled box, at this member
    refine LinComb.linComb_outer _ _ ⟨x₀, hx₀, exp (r • A) *ᵥ x₀, ?_, 1 - t / r, ?_, ?_⟩
    · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
        (MatExp.exp_mem_expIntervalEnclosure _ (m + 2)
          (Interval.smul_outer r sys.A hA) hε)
        (Set.mem_image_of_mem _ hx₀))
    · exact ⟨by linarith, by linarith⟩
    · rw [sub_sub_cancel]
  · -- and the curvature term is the box's correction matrix acting on `X₀`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expDiff_mem_intervalCorrectionMatrix sys.A hr hε hA ht0 htr)
      (Set.mem_image_of_mem _ hx₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
