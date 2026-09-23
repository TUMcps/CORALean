import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

/-!
# One sampled run of the closed loop

`simulate` samples one closed-loop run directly, no `enclose` needed: a point
computation, none of `reach`'s set instances required — no input argument,
since the controller supplies it, so a run is determined by its initial state
alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
    [Mtimes (Mat 𝕋) S] in
/-- One sampled run of the closed loop from `x₀` — no input argument, since the
controller supplies it: a run is determined by its initial state alone. -/
noncomputable def NeurNetContrSysDT.simulate (sys : NeurNetContrSysDT 𝕋 S n)
    (π : Vec ℝ n → Vec ℝ n) (x₀ : Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => toRealMat sys.plant.A *ᵥ sys.simulate π x₀ k + π (sys.simulate π x₀ k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
