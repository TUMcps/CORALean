import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable

/-!
# `inputSolution` contains the input's contribution at every time in the step

Thm. 3.1 encloses what the input contributes at the *end* of a step. A
time-interval enclosure needs one set covering every `t ∈ [0,r]`, and Prop. 3.3
says `0 ∈ U` makes those the same set.

Composing the two costs nothing beyond what Thm. 3.1 already asked, because the
monotonicity happens among sets of points and never among their enclosures —
`plus` and `mtimes` carry enclosure guarantees, not monotonicity.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
set_option maxHeartbeats 400000 in
/-- Thm. 3.1 as a statement about `inputReach`: the enclosure holds for every
admissible input at once, which is the form Prop. 3.3 composes with. -/
theorem LinearSys.inputReach_subset_inputSolution [Mtimes ℐ S]
    (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U))) :
    sys.inputReach U r ⊆ construct (sys.inputSolution r η U) := by
  rintro _ ⟨u, hmem, hmeas, rfl⟩
  refine sys.inputSolution_outer hr η hε hconv hclosed hbdd hRconv hRclosed hRbdd ?_
    (aestronglyMeasurable_reflect_Ioc hmeas)
  intro σ hσ
  exact hmem _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
set_option maxHeartbeats 400000 in
/-- Everything the input contributed up to any time in the step lies in the
enclosure computed for the whole step, once `U` contains the origin. -/
theorem LinearSys.Trajectory.inputSolution_timeInterval_outer
    [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by
  have hmemt : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ sys.inputReach U t :=
    ⟨u, fun s hs => traj.input s hs.1, traj.aestronglyMeasurable_input le_rfl, rfl⟩
  exact sys.inputReach_subset_inputSolution hr η hε hconv hclosed hbdd hRconv hRclosed hRbdd
    (sys.inputReach_mono hbdd h0 ht0 htr hmemt)

end CORALean.Real
