module

public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
public import CORALean.ContDynamics.LinParamSysDT.Operations.Simulate

@[expose] public section

/-!
# `simulate` samples a trajectory

`simulate A x₀ u` satisfies `Trajectory R₀ U` given `x₀ ∈ construct R₀`, `u`
staying in `construct U`, and `A k ∈ construct sys.A` at every `k`: `init` and
`input` are the hypotheses handed in, `step` is `⟨A k, hA k, rfl⟩`, since
`simulate`'s equation at `A k` is one witness of `Trajectory.step`'s `∃ A`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.simulate_trajectory (sys : LinParamSysDT 𝕄 n) {A : ℕ → Mat ℝ n n}
    (hA : ∀ k, A k ∈ construct sys.A) {R₀ U : S n} {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ construct R₀) {u : ℕ → Vec ℝ n} (hu : ∀ k, u k ∈ construct U) :
    sys.Trajectory R₀ U (sys.simulate A x₀ u) u where
  init := hx₀
  input := hu
  step k := ⟨A k, hA k, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
