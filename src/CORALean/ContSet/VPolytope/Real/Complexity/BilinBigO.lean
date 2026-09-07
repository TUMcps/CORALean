import CORALean.ContSet.VPolytope.Real.Complexity.Bilin
import CORALean.Global.Mathlib

/-!
# `bilin`'s vertex count is `O(m ^ 2)`

Not a bare arithmetic fact about `m * m`, but one tied to `bilin` through a
family of vertex sets whose sizes grow as `m`. `bilin_k` reduces the left side
to that product outright, which `m ^ 2` dominates for every `m`, so the bound
needs no filter condition beyond what `IsBigO.of_bound` always asks for.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.bilin_k_isBigO (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : ℕ → VPolytope α)
    (Q : ℕ → VPolytope β) (hP : ∀ m, (P m).k = m) (hQ : ∀ m, (Q m).k = m) :
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
