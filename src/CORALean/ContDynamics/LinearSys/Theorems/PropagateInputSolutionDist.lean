import CORALean.ContDynamics.LinearSys.Operations.PropagateInputSolution
import Mathlib.Analysis.Matrix.Normed

/-!
# One step's approximation error, summed over the horizon

The step of [1, Prop. 1]'s recursion adds `e^{A t_k}` applied to the one-step
set, so an error of at most `c` per step is carried across at most `M = max_k
‖e^{A t_k}‖` and the errors add: `ω` steps cost `ω · M · c`. Nothing about the
two sets is used beyond the one-step witness, so the same summation serves the
outer and the inner approximation.

With `c` of order `Δt²` and `ω = t/Δt` this is the whole of the proposition:
`ω · M · c` is of order `Δt`, and `M ≤ e^{‖A‖t}` uniformly in the step count.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A one-step witness at distance `c` gives a horizon witness at `ω · M · c`. -/
theorem LinearSys.propagateInputSolution_dist (sys : LinearSys 𝕋 n) (Δt : ℝ)
    {Z Z' : Set (Vec ℝ n)} {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ Z, ∃ y ∈ Z', ‖x - y‖ ≤ c) (ω : ℕ) :
    (∀ k : ℕ, k < ω → ‖exp (((k : ℝ) * Δt) • toRealMat sys.A)‖ ≤ M) →
      ∀ x ∈ sys.propagateInputSolution Δt Z ω,
        ∃ y ∈ sys.propagateInputSolution Δt Z' ω, ‖x - y‖ ≤ (ω : ℝ) * (M * c) := by -- --- PROOF ---
  induction ω with
  | zero =>
    intro _ x hx
    refine ⟨x, hx, ?_⟩
    simp
  | succ k ih =>
    intro hexp x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hb
    obtain ⟨a', ha', hda⟩ := ih (fun j hj => hexp j (by omega)) a ha
    obtain ⟨w, hw, hdz⟩ := h z hz
    refine ⟨a' + exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ w,
      Set.add_mem_add ha' ⟨w, hw, rfl⟩, ?_⟩
    -- the two errors separate, the second across the propagator of its own step
    have hsplit : a + exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ z
        - (a' + exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ w)
        = (a - a') + exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ (z - w) := by
      rw [Matrix.mulVec_sub]
      abel
    have hstep : ‖exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ (z - w)‖ ≤ M * c :=
      le_trans (Matrix.linfty_opNorm_mulVec _ _)
        (mul_le_mul (hexp k (by omega)) hdz (norm_nonneg _) hM)
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have : (k : ℝ) * (M * c) + M * c = ((k : ℕ) + 1 : ℕ) * (M * c) := by push_cast; ring
    rw [← this]
    exact add_le_add hda hstep

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
