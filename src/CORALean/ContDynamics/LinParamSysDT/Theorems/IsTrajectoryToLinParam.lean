module

public import CORALean.ContDynamics.LinParamSysDT.Operations.ToLinParam

@[expose] public section

/-!
# A `LinearSysDT` trajectory is a `toLinParam` trajectory

`LinearSysDT.IsCanonicalTrajectory.step`'s `x (k+1) = toRealMat sys.A *ᵥ x k + u k`,
repackaged as `LinParamSysDT.IsCanonicalTrajectory.step`'s existential: the witness is
`toRealMat sys.A` itself, and `construct sys.A = {toRealMat sys.A}` makes its
membership `rfl`.

## Inputs
* `sys` – linear system
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal

## Hypotheses
* `traj` – linear-system trajectory

## Conclusion
* the trajectory is a trajectory of the set-valued-matrix system
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.IsCanonicalTrajectory.toLinParam {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u) :
    sys.toLinParam.IsCanonicalTrajectory R₀ U x u where
  init := traj.init
  input := traj.input
  step k := ⟨toRealMat sys.A, rfl, traj.step k⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
