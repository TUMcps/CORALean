module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map

@[expose] public section

/-!
# One sampled run of the closed loop

`simulate` samples one closed-loop run directly, no `enclose` needed: a point
computation, none of `reach`'s set instances required — the controller supplies the network's
part of the input, so a run is determined by its initial state and its external input signal.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
    [Mtimes (Mat 𝕋) S] in
/-- One sampled run of the closed loop from `x₀` under the external input signal `v`: the
controller supplies the rest, so a run is determined by its initial state and `v`. -/
noncomputable def NeurNetContrSysDT.simulate (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (v : ℕ → Vec ℝ sys.nExt) (x₀ : Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => sys.map π (sys.simulate π v x₀ k) (v k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
