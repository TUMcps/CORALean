module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLeConZonotope

@[expose] public section

/-!
# `reach`'s degrees of freedom are `O(1)` in the step count, at `ConZonotope` too

Restates `reach_order_le_conZonotope` as growth, the shape `reach_h_isBigO` sets for `Zonotope`:
the generators beyond the equality rows, `h - mₑ`, stay below `o * n`, which carries no `k`. That is
the count CORA's `conZonotope/reduce` controls; the equality rows, and with them the generator
count, may grow with the run.

## Inputs
* `sys` – system
* `o` – maximum order
* `R₀` – initial constrained zonotope
* `U` – input constrained zonotope

## Hypotheses
* `ho` – order positive

## Conclusion
* the generators of the reachable set beyond its equality rows are bounded by a constant
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒞]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reach_h_isBigO_conZonotope (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Real.ConZonotope (Vec ℝ n)) : -- --- CONCL ---
    (fun k : ℕ => (((sys.reach (S := 𝒞) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h
      - (sys.reach (S := 𝒞) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).P.me : ℕ) : ℝ))
      =O[Filter.atTop] fun _ : ℕ => (1 : ℝ) := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound (o * n : ℝ)
  filter_upwards with k
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), mul_one]
  have := sys.reach_order_le_conZonotope ho R₀ U k
  exact_mod_cast (show _ - _ ≤ o * n by omega)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
