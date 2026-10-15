module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map

@[expose] public section

/-!
# One sampled run of the closed loop

`simulate` samples one closed-loop run directly, no `enclose` needed: a point
computation, none of `reach`'s set instances required — no input argument,
since the controller supplies it, so a run is determined by its initial state
alone.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
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
/-- One sampled run of the closed loop from `x₀` — no input argument, since the
controller supplies it: a run is determined by its initial state alone. -/
noncomputable def NeurNetContrSysDT.simulate (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.plant.m) (x₀ : Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => toRealMat sys.plant.A *ᵥ sys.simulate π x₀ k +
      toRealMat sys.plant.B *ᵥ π (sys.simulate π x₀ k) + toRealVec sys.plant.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
