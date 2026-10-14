module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `HPolytope.plusFullspaceCora`: `P + S` of `@polytope/plus.m` with a full space operand

`@polytope/plus.m` (l. 55-58) tests for the full space before the empty set is considered:

```
if representsa_(P,'fullspace',tol) || representsa_(S,'fullspace',tol)
    S_out = polytope.Inf(n); return
end
if isa(S,'polytope')
    if representsa_(P,'emptySet',tol) || representsa_(S,'emptySet',tol)
        S_out = polytope.empty(n); return
```

The Minkowski sum `P ⊕ S = {p + s | p ∈ P, s ∈ S}` with an empty operand is empty, whatever the
other operand is. For `P` the full space and `S` empty, the first test fires and the result is the
full space. The sets are subsets of `R^n`, given by their points; `polytope.Inf(n)` is the full
set. Read from the source, not run.

# CORA's `polytope.Inf(2) + polytope.empty(2)` is the full space

The sum with the empty set has no points, but CORA returns `polytope.Inf(2)`. Read from the
source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The point set of CORA's `P + S` for two polytopes of `R^n` that are given as point sets. -/
def HPolytope.plusFullspaceCora {n : ℕ} (P S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  -- representsa_(P,'fullspace',tol) || representsa_(S,'fullspace',tol)
  if P = Set.univ ∨ S = Set.univ then Set.univ
  -- the sum of the two sets
  else {x | ∃ p ∈ P, ∃ s ∈ S, x = p + s}

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For every dimension, the full space plus the empty set is the full space for CORA, although
the sum of any set with the empty set has no point. -/
theorem HPolytope.plusFullspace_cora_counterexample (n : ℕ) :
    HPolytope.plusFullspaceCora (Set.univ : Set (Fin n → ℝ)) ∅ = Set.univ ∧
      {x : Fin n → ℝ | ∃ p ∈ (Set.univ : Set (Fin n → ℝ)), ∃ s ∈ (∅ : Set (Fin n → ℝ)),
        x = p + s} = ∅ := by
  refine ⟨by simp [HPolytope.plusFullspaceCora], ?_⟩
  ext x
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
