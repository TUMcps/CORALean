import CORALean.Specification.Operations.VerifyConvexStep

/-!
# [1, Alg. 3]: a GJK-style search for a separating or an intersecting direction

The two conclusive exits of `Alg. 3` — line 4-5 (`safe`) and line 12-13 (`unsafe`) — folded
over a caller-supplied direction sequence `ℓ` and a fuel bound, since the search loop need not
terminate. The Gram-Schmidt direction search of lines 18-25 and the `falsifiable`/`Δt`-halving
restart of lines 7, 14-16 only ever change which direction is tried next, never whether a taken
exit is sound, so neither is modelled here. `ℓ i` is read against one reachable set `O` and one
unsafe set `U`: the paper's `R̂(t)` (a `SupportBound`, line 4) and `R̲(t)` (a `SupportWitness`,
line 10) become one bound and one witness on the same `O`.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: fold `verifyConvexStep` over `fuel` directions drawn from
`ℓ`, starting undecided with nothing accumulated. -/
noncomputable def verifyConvex (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ) :
    VerifyAnswer :=
  ((List.range fuel).foldl (verifyConvexStep bO bU wO wU ℓ)
    (.undecided, (∅ : Set α))).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
