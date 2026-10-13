import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOrderLe
import Mathlib.Analysis.Asymptotics.Defs

/-!
# `reach`'s size is `O(1)` in the step count

`LinearSysDT.reach_h_isBigO`'s statement and proof, character for character, at
a set-valued `sys.A`: reduction is still what holds the generator count
independent of `k`, and `reach_order_le`'s `o * n` is still the bound behind it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [Mtimes 𝕄 𝒵]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reach_h_isBigO (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) :
    (fun k : ℕ => (((sys.reach (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h : ℕ) : ℝ))
      =O[Filter.atTop] fun _ : ℕ => (1 : ℝ) := by
  apply Asymptotics.IsBigO.of_bound (o * n : ℝ)
  filter_upwards with k
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), mul_one]
  exact_mod_cast sys.reach_order_le ho R₀ U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
