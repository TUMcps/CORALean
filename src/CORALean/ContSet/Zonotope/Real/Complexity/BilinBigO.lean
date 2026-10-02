import CORALean.ContSet.Zonotope.Real.Complexity.Bilin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Positivity

/-!
# `bilin`'s cost is `O(m ^ 2)`

The shape the rest of `Complexity/` should eventually take: not a bare
arithmetic fact about `m + m + m * m`, but one tied to `bilin` through a family
of zonotopes whose sizes grow as `m`. `bilin_h` reduces the left side to that
sum, which `3 * m ^ 2` dominates for every `m`, so the bound needs no filter
condition — `IsBigO.of_bound` still asks for one only eventually.

`Asymptotics.IsBigO.of_bound` closes it: it asks for domination by a fixed
constant `∀ᶠ x in l`, which the whole range `m ≥ 1` clears with room to spare.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.bilin_h_isBigO (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (Z : ℕ → Zonotope α) (W : ℕ → Zonotope β)
    (hZ : ∀ m, (Z m).h = m) (hW : ∀ m, (W m).h = m) :
    (fun m : ℕ => (((Zonotope.bilin f (Z m) (W m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hh : (Zonotope.bilin f (Z m) (W m)).h = m + m + m * m := by
    rw [Zonotope.bilin_h, hZ, hW]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hh, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
