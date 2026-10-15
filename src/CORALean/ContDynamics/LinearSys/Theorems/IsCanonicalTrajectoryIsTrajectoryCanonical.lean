module

public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# Every run of the canonical form is a run of a full system

The converse of `IsTrajectory.canonical`: a `IsCanonicalTrajectory` of `sys` is a `IsTrajectory` of
`LinearSys.canonical A`, the system `(A, I, 0, I, 0, 0, 0, I)` at `sys`'s own `A`, with no
disturbance or noise and the state as output. Together the two say the canonical form loses no
run and adds none. Stated at ℝ, where `1` and `0` read as themselves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run itself, with zero disturbance and noise, which `W` and `V` have to admit. -/
theorem LinearSys.IsCanonicalTrajectory.isTrajectory_canonical {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory T R₀ U x u) {W V : S n}
    (hW : (0 : Vec ℝ n) ∈ construct W) (hV : (0 : Vec ℝ n) ∈ construct V) :
    (LinearSys.canonical (toRealMat sys.A)).IsTrajectory T R₀ U W V x u 0 0 x where
  init := traj.init
  input := traj.input
  dist _ _ := hW
  noise _ _ := hV
  meas := traj.meas
  measDist := aestronglyMeasurable_const
  cont := traj.cont
  -- `I u + 0 + 0 w` is `u`
  flow t ht := by
    rw [traj.flow t ht]
    simp [LinearSys.canonical]
  -- `I x + 0 u + 0 + I 0` is `x`
  output t _ := by
    show x t = (1 : Mat ℝ n n) *ᵥ x t + (0 : Mat ℝ n n) *ᵥ u t + 0 + (1 : Mat ℝ n n) *ᵥ 0
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
