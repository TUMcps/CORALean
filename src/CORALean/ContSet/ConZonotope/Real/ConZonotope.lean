module

public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.UnitBox
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Block

@[expose] public section

/-!
# Constrained zonotopes: the representation

CORA's `conZonotope` [1, Def. 3]: a zonotope whose coefficients are cut down further. The
cutting is an `HPolytope` over the coefficient space rather than the matrix
equation `A β = b`, so the constraints *are* a polytope rather than merely
denoting one, and every polytope operation applies to them directly —
`ofMat` recovers CORA's form, and `plus` and `mtimesIntervalMat` state their
constraints by `comap` and `intersection` instead of assembling matrix rows.

That generalizes CORA, which admits equalities only. Inequalities cost nothing
here and a halfspace description carries both.

The unit box stays outside `P`, imposed by `construct`: it is what makes the
coefficients a zonotope's, and keeping it separate is what lets `zonotope` be an
enclosure whatever `P` says.

Over any real module, as a zonotope is: the constraints live on the coefficient
space `Vec ℝ h`, whatever the generators point into.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure ConZonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α
  /-- What the coefficients must satisfy beyond `|βⱼ| ≤ 1`. -/
  P : HPolytope (Vec ℝ h)

def ConZonotope.construct (cZ : ConZonotope α) : Set α :=
  {x | ∃ β : Fin cZ.h → ℝ, (∀ j, |β j| ≤ 1) ∧ β ∈ cZ.P.construct
        ∧ x = cZ.c + ∑ j, β j • cZ.G j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
