module

public import CORALean.Specification.Operations.VerifyConvexStep

@[expose] public section

/-!
# [1, Alg. 3 (exits)]: a GJK-style search for a separating or an intersecting direction

The two conclusive exits of `Alg. 3` — line 4-5 (`safe`) and line 12-13 (`unsafe`) — folded
over a caller-supplied direction sequence `ℓ` and a fuel bound, since the search loop need not
terminate. The Gram-Schmidt direction search of lines 18-25 and the `falsifiable`/`Δt`-halving
restart of lines 7, 14-16, [1, Alg. 3 (search)], only ever change which direction is tried
next, never whether a taken exit is sound, so neither is modelled here. `ℓ i` is read against
one reachable set `O` and one unsafe set `U`: the paper's `R̂(t)` (a `SupportBound`, line 4)
and `R̲(t)` (a `SupportWitness`, line 10) become one bound and one witness on the same `O`.

Real-only, a specification: it decides from bounds and witnesses supplied as oracles over every
direction, and its soundness is the theorem.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (exits)]: fold `verifyConvexStep` over `fuel` directions drawn from
`ℓ`, starting undecided with nothing accumulated. -/
noncomputable def verifyConvex (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ) :
    VerifyAnswer :=
  -- 1. `P̌ ← ∅` (and no answer yet)
  let init : VerifyAnswer × Set α := (.undecided, ∅)
  -- 2. `repeat`: lines 4-13 once per direction `ℓᵢ`, `fuel` times at most
  let final := (List.range fuel).foldl (verifyConvexStep bO bU wO wU ℓ) init
  -- 5., 13. the answer a pass reached, `safe` or `unsafe`; `undecided` once `fuel` is spent
  final.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
