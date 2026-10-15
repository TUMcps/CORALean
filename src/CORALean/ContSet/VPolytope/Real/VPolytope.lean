module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Polytopes: the vertex representation

The definition is [1, Def. 1]; [2, Def. 3] restates it beside the halfspace form.

CORA's `polytope` with `isVRep` set: the convex hull of finitely many points,
written here as the convex combinations of them.

Over any real module, as a zonotope is, and for the same reason — nothing about
a convex combination mentions coordinates. Only the coefficient constraint
differs: `∑ βⱼ = 1` with `βⱼ ≥ 0` here, `|βⱼ| ≤ 1` there.

Zero vertices denote `∅`, no coefficient family over an empty index summing
to one.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
* [2] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure VPolytope (α : Type) where
  k : ℕ
  V : Fin k → α

def VPolytope.construct (P : VPolytope α) : Set α :=
  {x | ∃ β : Fin P.k → ℝ, (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 ∧ x = ∑ j, β j • P.V j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
