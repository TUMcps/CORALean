import CORALean.Specification.Definitions.VerifyAnswer
import CORALean.Specification.Operations.DiffPoint
import Mathlib.Analysis.Convex.Hull

/-!
# [1, Alg. 3, l. 4-13]: one direction of the search

`verifyConvexStep`: `safe` once the bounds separate, `violated` once the accumulated hull
reaches the origin, else the new point is folded in. A reached answer is carried forward,
extra fuel harmless.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3, l. 4-13] for one direction `ℓ i`: `safe` once the bounds
separate, `violated` once the accumulated hull reaches the origin, else the
new point is folded in. A reached answer is carried forward, extra fuel harmless. -/
noncomputable def verifyConvexStep (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) :
    VerifyAnswer × Set α → ℕ → VerifyAnswer × Set α
  | (.safe, V), _ => (.safe, V)
  | (.violated, V), _ => (.violated, V)
  | (.undecided, V), i =>
      if (bO (ℓ i)).val + (bU (-(ℓ i))).val < 0 then (.safe, V)
      else
        let V' := insert (diffPoint wO wU (ℓ i)) V
        if (0 : α) ∈ convexHull ℝ V' then (.violated, V') else (.undecided, V')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
