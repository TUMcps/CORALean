module

public import CORALean.Specification.Operations.VerifyConvex
public import CORALean.Specification.Theorems.VerifyConvexFoldInv

@[expose] public section

/-!
# A `safe` verdict from `verifyConvex` names a separating direction

`exists_separating_of_verifyConvex_eq_safe`: a `safe` answer from [1, Alg. 3 (exits)] came from the
bounds already separating along some direction the search tried.

## Inputs
* `bO` – bounds of the reachable set
* `bU` – bounds of the unsafe set
* `wO` – witnesses of the reachable set
* `wU` – witnesses of the unsafe set
* `ℓ` – sequence of directions
* `fuel` – number of directions tried

## Hypotheses
* `h` – the search answers safe

## Conclusion
* some direction separates the bounds of the two sets

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `safe` answer came from the bounds already separating along some
direction the search tried. -/
theorem exists_separating_of_verifyConvex_eq_safe (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ)
    (h : verifyConvex bO bU wO wU ℓ fuel = .safe) :
    ∃ c : α →ₗ[ℝ] ℝ, (bO c).val + (bU (-c)).val < 0 :=
  (verifyConvexFold_inv bO bU wO wU ℓ (List.range fuel)
    (Set.empty_subset _) (fun h => by cases h) (fun h => by cases h)).2.2 h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
