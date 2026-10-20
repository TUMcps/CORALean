module

public import CORALean.ContSet.VPolytope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.VPolytope.Real.Complexity.Space.Theorems.BilinK

@[expose] public section

/-!
# `VPolytope.bilin_k_isBigO`

The `k` count of `bilin`'s result in `O`-notation.

## Inputs
* `f` – bilinear map
* `P` – polytopes with `m` vertices
* `Q` – polytopes with `m` vertices

## Hypotheses
* `hP` – `P m` has `m` vertices
* `hQ` – `Q m` has `m` vertices

## Conclusion
* the vertex count of `bilin` grows like `m²`
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `k` count of `bilin`'s result in `O`-notation. -/
theorem VPolytope.bilin_k_isBigO (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : ℕ → VPolytope α)
    (Q : ℕ → VPolytope β) (hP : ∀ m, (P m).k = m) (hQ : ∀ m, (Q m).k = m) : -- --- CONCL ---
    (fun m : ℕ => (((VPolytope.bilin f (P m) (Q m)).k : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hk : (VPolytope.bilin f (P m) (Q m)).k = m * m := by
    rw [VPolytope.bilin_k, hP, hQ]
  rw [hk, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg (m : ℝ)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
