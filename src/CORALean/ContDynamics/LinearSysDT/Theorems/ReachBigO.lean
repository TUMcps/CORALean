import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOrderLe
import CORALean.Global.Mathlib

/-!
# `reach`'s size is `O(1)` in the step count

Without `reduce` in the loop the count would grow with `k`: one `plus` per step
adds `U`'s generators (`plus_h`), one `mtimes` keeps the count (`mtimes_h`), so
nothing shrinks it back. It is reduction alone that holds a reachable set's
size independent of how long the run goes — `reach_order_le`'s `o * n`, with no
`k` in it, is that fact; this restates it as growth, the shape
`bilin_h_isBigO` set for the rest of `Complexity/`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒵]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reach_h_isBigO (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) :
    (fun k : ℕ => (((sys.reach (S := 𝒵) o ho R₀ U (k + 1)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun _ : ℕ => (1 : ℝ) := by
  apply Asymptotics.IsBigO.of_bound (o * n : ℝ)
  filter_upwards with k
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), mul_one]
  exact_mod_cast sys.reach_order_le ho R₀ U k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
