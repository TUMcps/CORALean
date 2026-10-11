import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.Operations.DeltaReach

/-!
# `deltaReach` contains every difference the step can span

`timeIntervalStep_outer_at`'s statement about the *difference* rather than the
state: at every `t` of `[0, r]`, `e^{At}x₀ - x₀` is in the set, and at `t = 0`
that is the origin, which is what makes the anchored segment right.

The split is the same one and by the same lemma. `e^{At} - I` is the straight
line from `0` to `e^{Ar} - I` at weight `t/r`, plus
`e^{At} - I - (t/r)(e^{Ar} - I)` — the very matrix `correctionMatrix` encloses,
so the second-order term is paid for once and serves both statements.

Homogeneous only: with a non-zero input the difference also picks up the input
integral, which is `TrajectoryDeltaReachOuter`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every difference between a state of the step and the state it started
from. -/
theorem LinearSys.deltaReach_outer (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀ - x₀) '' construct X₀
      ⊆ construct (sys.deltaReach r (m + 2) X₀) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  rintro y ⟨x₀, hx₀, rfl⟩
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  -- the far end of the segment, and the origin as its own zero image
  have hD : (exp (r • A) - 1) *ᵥ x₀ ∈ construct (Mtimes.mtimes (exp (r • A) - 1) X₀) :=
    Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx₀))
  have hO : (0 : Vec ℝ n) ∈ construct (Mtimes.mtimes (0 : Mat ℝ n n)
      (Mtimes.mtimes (exp (r • A) - 1) X₀)) := by
    have h := Mtimes.mtimes_outer (0 : Mat ℝ n n) (Mtimes.mtimes (exp (r • A) - 1) X₀)
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hD))
    simpa using h
  -- the difference is that segment plus what the curvature adds
  have hdecomp : exp (t • A) *ᵥ x₀ - x₀
      = ((1 - t / r) • (0 : Vec ℝ n) + (t / r) • ((exp (r • A) - 1) *ᵥ x₀))
        + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x₀ := by
    simp only [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, smul_zero, zero_add]
    abel
  show exp (t • A) *ᵥ x₀ - x₀ ∈ _
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · exact LinComb.linComb_outer _ _ ⟨0, hO, (exp (r • A) - 1) *ᵥ x₀, hD, 1 - t / r,
      ⟨by linarith, by linarith⟩, by rw [sub_sub_cancel]⟩
  · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expDiff_mem_correctionMatrix A hr hε ht0 htr)
      (Set.mem_image_of_mem _ hx₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
