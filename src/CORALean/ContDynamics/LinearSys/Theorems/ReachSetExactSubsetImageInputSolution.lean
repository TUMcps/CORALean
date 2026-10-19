module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

@[expose] public section

/-!
# The time-point reachable set inside an exact sum, not a representation

`reachSetExact_subset_timeInterval_inputSolution` encloses `reachSetExact T R₀ U t` in
`construct (Plus.plus (timeIntervalStep ...) (inputSolution ...))`, paying for
the whole step's wrapping effect even at `t = r`, the step's end. What a
trajectory gives there instead: `variation_of_constants` splits `x r` into
`e^{Ar} x 0`, exact, and the input's integral, inside `inputReach`, which
`inputReach_subset_inputSolution` [1, Thm. 1] encloses — no `timeIntervalStep`,
no hull, and `+` the genuine Minkowski sum, exactly what `LinearSys.timePointBound`
needs.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to enclose the whole time-point reachable set by a genuine
sum of an exact image and a set; for `reachSetExact_subset_timeInterval_inputSolution`
where a computed representation is what is wanted instead. -/
theorem LinearSys.reachSetExact_subset_image_inputSolution (sys : LinearSys 𝕋 n) {T : Set ℝ}
    (R₀ U : S n) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U))) : -- --- CONCL ---
    sys.reachSetExact T R₀ U r
      ⊆ (exp (r • toRealMat sys.A)).mulVecLin '' construct R₀
        + construct (sys.inputSolution r η U) := by -- --- PROOF ---
  rintro _ ⟨x, u, traj, rfl⟩
  have hmem : (∫ s in (0:ℝ)..r, exp ((r - s) • toRealMat sys.A) *ᵥ u s)
      ∈ sys.inputReach U r :=
    ⟨u, fun s hs => traj.input s (hT hs), traj.aestronglyMeasurable_input hT, rfl⟩
  have hvoc := traj.variation_of_constants hT le_rfl hr.le hbdd
  rw [sub_zero] at hvoc
  rw [hvoc]
  refine Set.add_mem_add ?_ (sys.inputReach_subset_inputSolution hr η hε hconv hclosed hbdd
    hRconv hRclosed hRbdd hmem)
  simp only [Set.mem_image, Matrix.mulVecLin_apply]
  exact ⟨x 0, traj.init, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
