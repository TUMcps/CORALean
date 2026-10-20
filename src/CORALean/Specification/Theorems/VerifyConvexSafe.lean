module

public import CORALean.Specification.Operations.VerifyConvex
public import CORALean.Specification.Theorems.ExistsSeparatingOfVerifyConvexEqSafe
public import CORALean.Specification.Theorems.Separation

@[expose] public section

/-!
# [1, Alg. 3 (exits), l. 4-5]: `verifyConvex`'s `safe` answer is sound

`exists_separating_of_verifyConvex_eq_safe` names the direction the search
stopped at; `Specification.holds_unsafeSet_of_separating` is exactly what a
separating direction buys. Nothing about the search itself — which direction,
or how many steps it took — survives into the statement.

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
* the unsafe set specification holds of the reachable set

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (exits)]: a `safe` answer from `verifyConvex` means the reachable set
and the unsafe set really are disjoint. -/
theorem Specification.holds_unsafeSet_of_verifyConvex_safe
    (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d) (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d)
    (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d) (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d)
    (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ) (h : verifyConvex bO bU wO wU ℓ fuel = .safe) :
    (Specification.unsafeSet U).Holds O :=
  let ⟨c, hc⟩ := exists_separating_of_verifyConvex_eq_safe bO bU wO wU ℓ fuel h
  Specification.holds_unsafeSet_of_separating (bO c) (bU (-c)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
