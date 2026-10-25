module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Polytopes: the halfspace representation

The definition is [1, Def. 2]; [2, Def. 3] restates it beside the vertex form. CORA's `polytope`
with `isHRep` set: the points satisfying finitely many inequalities `A x ≤ b` and equalities
`Ae x = be`. A constraint is a linear functional rather than a matrix row, so the representation
lives at any real module; `ofMat` reads CORA's matrices into it.

Exact under intersection and preimage, and under nothing else: a Minkowski sum or a convex hull
of two halfspace descriptions needs vertex enumeration. That is what `VPolytope` is for, the two
representations being good at disjoint operations.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
* [2] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

/-- A polytope given by halfspaces: inequalities `A x ≤ b` and equalities `Ae x = be`. -/
structure HPolytope (α : Type) [AddCommGroup α] [Module ℝ α] where
  m : ℕ
  A : Fin m → (α →ₗ[ℝ] ℝ)
  b : Fin m → ℝ
  me : ℕ
  Ae : Fin me → (α →ₗ[ℝ] ℝ)
  be : Fin me → ℝ

/-- The set a halfspace description denotes: the points satisfying all inequalities and all
equalities. -/
def HPolytope.construct (P : HPolytope α) : Set α :=
  {x | (∀ i, P.A i x ≤ P.b i) ∧ ∀ i, P.Ae i x = P.be i}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
