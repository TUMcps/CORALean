import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable

/-!
# `inputSolution` contains the input's contribution at every time in the step

Thm. 3.1 encloses what the input contributes at the *end* of a step, which is
all a sampled guarantee needs. A time-interval enclosure needs one set covering
every `t ∈ [0,r]`, and Prop. 3.3 says `0 ∈ U` makes those the same set.

Assembled as the thesis assembles it: `inputReach_subset_inputSolution` is
Thm. 3.1 read as a statement about `inputReach`, and `inputReach_mono` is
Prop. 3.3. Composing them needs nothing about the representation beyond what
Thm. 3.1 already asked, because the monotonicity happens among sets of points
and never among their enclosures — which is what makes it available at all, as
`plus` and `mtimes` carry enclosure guarantees rather than monotonicity.
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
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OuterContSet S ℝ]

set_option maxHeartbeats 400000 in
/-- Thm. 3.1 as a statement about `inputReach`: the enclosure holds for every
admissible input at once, which is the form Prop. 3.3 composes with. -/
theorem LinearSys.inputReach_subset_inputSolution [Mtimes IntervalMat S]
    (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U))) :
    sys.inputReach U r ⊆ construct (sys.inputSolution r η U) := by
  rintro _ ⟨u, hmem, hmeas, rfl⟩
  refine sys.inputSolution_outer hr η hε hconv hclosed hbdd hRconv hRclosed hRbdd ?_
    (aestronglyMeasurable_reflect_Ioc hmeas)
  intro σ hσ
  exact hmem _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩

set_option maxHeartbeats 400000 in
/-- Everything the input contributed up to any time in the step lies in the
enclosure computed for the whole step, once `U` contains the origin. -/
theorem LinearSys.Trajectory.inputSolution_timeInterval_outer [Mtimes IntervalMat S]
    {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)))
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
