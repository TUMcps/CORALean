import CORALean.ContSet.PolyZonotope.Real.Complexity.Bilin
import CORALean.Global.Mathlib

/-!
# `PolyZonotope.bilin`'s dependent-generator count is `O(m ^ 2)`

Not a bare arithmetic fact about `(m+1)*(m+1)`, but one tied to `bilin` through
a family of sets whose dependent-generator counts grow as `m`. `bilin_h`
reduces the left side to that product, which `4 * m ^ 2` dominates for every
`m ≥ 1`.

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

theorem PolyZonotope.bilin_h_isBigO (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (S : ℕ → PolyZonotope α)
    (T : ℕ → PolyZonotope β) (hp : ∀ m, (S m).p = (T m).p) (hS : ∀ m, (S m).h = m)
    (hT : ∀ m, (T m).h = m) :
    (fun m : ℕ => (((PolyZonotope.bilin f (S m) (T m) (hp m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hh : (PolyZonotope.bilin f (S m) (T m) (hp m)).h = (m + 1) * (m + 1) := by
    rw [PolyZonotope.bilin_h, hS, hT]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hh, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
