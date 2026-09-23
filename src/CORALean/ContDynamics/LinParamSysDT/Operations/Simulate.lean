import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# One sampled run, at a chosen matrix per step

`simulate` takes the matrix at each step as an argument, one point computation
per step chosen from `sys.A`, and carries no set instance of its own — the
concrete meaning of `step`'s `∃ A ∈ construct sys.A`; not a field of `sys`,
since it is chosen afresh each run.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sampled run of the dynamics from `x₀` under `u`, at a matrix `A k`
chosen per step — the concrete meaning of `step`'s `∃ A ∈ construct sys.A`;
not a field of `sys`, since it is chosen afresh each run. -/
def LinParamSysDT.simulate (sys : LinParamSysDT 𝕄 n) (A : ℕ → Mat ℝ n n)
    (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => A k *ᵥ sys.simulate A x₀ u k + u k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
