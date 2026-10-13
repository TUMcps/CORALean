import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLeConZonotope

/-!
# `reach`'s size is `O(1)` in the step count, at `ConZonotope` too

Restates `reach_order_le_conZonotope` as growth, the shape `reach_h_isBigO`
sets for `Zonotope`: the bound `o * n` carries no `k`, so the generator count
of a `ConZonotope` reachable set is bounded independent of how long the run
goes, the same fact `reduce` in the loop buys at either representation.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒞]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reach_h_isBigO_conZonotope (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Real.ConZonotope (Vec ℝ n)) :
    (fun k : ℕ => (((sys.reach (S := 𝒞) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h : ℕ) : ℝ))
      =O[Filter.atTop] fun _ : ℕ => (1 : ℝ) := by
  apply Asymptotics.IsBigO.of_bound (o * n : ℝ)
  filter_upwards with k
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), mul_one]
  exact_mod_cast sys.reach_order_le_conZonotope ho R₀ U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
