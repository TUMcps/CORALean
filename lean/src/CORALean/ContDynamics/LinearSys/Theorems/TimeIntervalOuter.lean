import CORALean.ContDynamics.LinearSys.Operations

/-!
# `timeIntervalStep` contains the flow at every time in the step

CORA's `HR([0,r]) = CH(X₀, e^{Ar}X₀) ⊕ F X₀`, and the guarantee that makes it
usable: not just at the sample times, but at every `t` in `[0, r]`.

The flow splits into the straight line from `X₀` to `e^{Ar}X₀`, which is a
`linComb` at weight `1 - t/r`, and the interpolation error, which is the
correction matrix acting on `X₀`. Neither half knows what representation it is
over — the two operations carry their own guarantees.

Homogeneous only: with a non-zero input a trajectory also picks up the input
integral, which is a separate term and a separate theorem.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OuterContSet S ℝ]
variable [Mtimes IntervalMat S]

set_option maxHeartbeats 1000000 in
theorem LinearSys.timeIntervalStep_outer (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timeIntervalStep r (m + 2) X₀) := by
  set A := toRealMat sys.A with hA
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
  refine OuterContSet.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the straight line is a segment between `X₀` and its image
    refine OuterContSet.linComb_outer _ _ ⟨x₀, hx₀, exp (r • A) *ᵥ x₀, ?_, 1 - t / r, ?_, ?_⟩
    · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx₀))
    · exact ⟨by linarith, by linarith⟩
    · rw [sub_sub_cancel]
  · -- and the curvature term is the correction matrix acting on `X₀`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (IntervalMat.expDiff_mem_correctionMatrix A hr hε ht0 htr)
      (Set.mem_image_of_mem _ hx₀))

end CORALean.Real
