module

public import CORALean.Specification.Operations.VerifyConvex
public import CORALean.Specification.Theorems.VerifyConvexFoldInv

@[expose] public section

/-!
# A `violated` verdict from `verifyConvex` names a witnessing hull

`exists_convexHull_of_verifyConvex_eq_unsafe`: an `unsafe` answer from [1, Alg. 3 (exits)]
came from a finite set of accumulated `O - U` points whose hull already reaches the origin.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
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

/-- An `unsafe` answer came from a finite set of accumulated `O - U` points
whose hull already reaches the origin. -/
theorem exists_convexHull_of_verifyConvex_eq_unsafe (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ)
    (h : verifyConvex bO bU wO wU ℓ fuel = .violated) : -- --- CONCL ---
    ∃ V : Set α, V ⊆ O - U ∧ (0 : α) ∈ convexHull ℝ V :=
  let inv := verifyConvexFold_inv bO bU wO wU ℓ (List.range fuel)
    (Set.empty_subset _) (fun h => by cases h) (fun h => by cases h)
  ⟨_, inv.1, inv.2.1 h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
