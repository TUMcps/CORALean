module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# `timeIntervalStep`'s content one step before the representation lifts

`timeIntervalStep_outer`, the wrapping-effect-free construction of [1, Alg. 1],
ends on two representation calls: `LinComb.linComb_outer` turns the straight
line from `X₀` to its image into a hull, `Plus.plus_outer` turns the sum of
that hull and the curvature term into `timeIntervalStep`. Held back, the
straight line is a genuine `Set.linComb` between `construct X₀` and its exact
image, and only the curvature term still needs `Mtimes`, which has no
set-level form to fall back to. `timeIntervalStep_outer` is this composed with
those two lifts.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every time of the step,
inside the exact sum `timeIntervalStep_outer` only reaches after two lifts. -/
theorem LinearSys.timeIntervalStep_outer_setLinComb (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ Set.linComb (construct X₀) ((exp (r • toRealMat sys.A)).mulVecLin '' construct X₀)
        + construct (Mtimes.mtimes (𝕄 := ℐ)
            (MatExp.correctionMatrix (toRealMat sys.A) r (m + 2)) X₀) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  rintro y ⟨x₀, hx₀, rfl⟩
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  have hdecomp : exp (t • A) *ᵥ x₀
      = ((1 - t / r) • x₀ + (t / r) • (exp (r • A) *ᵥ x₀))
        + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x₀ := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_smul, smul_sub, one_smul]
    abel
  show exp (t • A) *ᵥ x₀ ∈ _
  rw [hdecomp]
  exact Set.add_mem_add
    ⟨x₀, hx₀, exp (r • A) *ᵥ x₀, Set.mem_image_of_mem _ hx₀, 1 - t / r,
      ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
    (Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expDiff_mem_correctionMatrix A hr hε ht0 htr) (Set.mem_image_of_mem _ hx₀)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
