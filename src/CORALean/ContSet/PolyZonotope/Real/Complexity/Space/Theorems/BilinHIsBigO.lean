module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.Basic

@[expose] public section

/-!
# `PolyZonotope.bilin_h_isBigO`

The `h` count of `bilin`'s result in `O`-notation.

## Inputs
* `f` – bilinear map
* `pZ` – sequence of polynomial zonotopes
* `T` – sequence of second polynomial zonotopes

## Hypotheses
* `hp` – factor counts agree
* `hS` – first has m generators
* `hT` – second has m generators

## Conclusion
* generator count grows at most quadratically
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `bilin`'s result in `O`-notation. -/
theorem PolyZonotope.bilin_h_isBigO (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ : ℕ → PolyZonotope α)
    (T : ℕ → PolyZonotope β) (hp : ∀ m, (pZ m).p = (T m).p) (hS : ∀ m, (pZ m).h = m)
    (hT : ∀ m, (T m).h = m) : -- --- CONCL ---
    (fun m : ℕ => (((PolyZonotope.bilin f (pZ m) (T m) (hp m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hh : (PolyZonotope.bilin f (pZ m) (T m) (hp m)).h = (m + 1) * (m + 1) := by
    rw [PolyZonotope.bilin_h, hS, hT]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hh, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
