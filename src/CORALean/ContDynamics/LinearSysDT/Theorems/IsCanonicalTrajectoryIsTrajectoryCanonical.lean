module

public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical

@[expose] public section

/-!
# Every run of the canonical form is a run of a full system

The converse of `IsTrajectory.canonical`: an `IsCanonicalTrajectory` of `sys` is an `IsTrajectory`
of `LinearSysDT.canonical A` at `sys`'s own `A`, with no disturbance or noise and the state as
output. Together the two say the canonical form loses no run and adds none. Stated at ℝ, where
`1` and `0` read as themselves.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `W` – disturbance set
* `V` – noise set

## Hypotheses
* `traj` – canonical trajectory
* `hW` – zero lies in the disturbance set
* `hV` – zero lies in the noise set

## Conclusion
* the run is a trajectory of the canonical full system
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run itself, with zero disturbance and noise, which `W` and `V` have to admit. -/
theorem LinearSysDT.IsCanonicalTrajectory.isTrajectory_canonical {sys : LinearSysDT 𝕋 n}
    {R₀ U : S n} {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u) {W V : S n}
    (hW : (0 : Vec ℝ n) ∈ construct W) (hV : (0 : Vec ℝ n) ∈ construct V) :
    (LinearSysDT.canonical (toRealMat sys.A)).IsTrajectory R₀ U W V x u 0 0 x where
  init := traj.init
  input := traj.input
  dist _ := hW
  noise _ := hV
  -- `I u + 0 + 0 w` is `u`
  step k := by
    show x (k + 1) = toRealMat sys.A *ᵥ x k + (1 : Mat ℝ n n) *ᵥ u k + 0 + (0 : Mat ℝ n n) *ᵥ 0
    rw [traj.step k]
    simp
  -- `I x + 0 u + 0 + I 0` is `x`
  output k := by
    show x k = (1 : Mat ℝ n n) *ᵥ x k + (0 : Mat ℝ n n) *ᵥ u k + 0 + (1 : Mat ℝ n n) *ᵥ 0
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
