import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution

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
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- Everything the input contributed up to any time in the step lies in the
enclosure computed for the whole step, once `U` contains the origin. -/
theorem LinearSys.Trajectory.inputSolution_timeInterval_outer
    [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory T R₀ U x u) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    -- `0 ∈ U` is what `inputReach_mono` needs, and the only extra hypothesis here
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have hmemt : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ sys.inputReach U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), traj.aestronglyMeasurable_input hTt, rfl⟩
  exact sys.inputReach_subset_inputSolution hr η hε hconv hclosed hbdd hRconv hRclosed hRbdd
    (sys.inputReach_mono hbdd h0 ht0 htr hmemt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
