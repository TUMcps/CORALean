import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.UnitBox
import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Block

/-!
# Constrained zonotopes: the representation

CORA's `conZonotope`: a zonotope whose coefficients are cut down further. The
cutting is an `HPolytope` over the coefficient space rather than the matrix
equation `A β = b`, so the constraints *are* a polytope rather than merely
denoting one, and every polytope operation applies to them directly —
`ofMat` recovers CORA's form, and `plus` and `mtimesIntervalMat` state their
constraints by `comap` and `and` instead of assembling matrix rows.

That generalizes CORA, which admits equalities only. Inequalities cost nothing
here and a halfspace description carries both.

The unit box stays outside `P`, imposed by `construct`: it is what makes the
coefficients a zonotope's, and keeping it separate is what lets `zonotope` be an
enclosure whatever `P` says.

Over any real module, as a zonotope is: the constraints live on the coefficient
space `Vec ℝ h`, whatever the generators point into.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure ConZonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α
  /-- What the coefficients must satisfy beyond `|βⱼ| ≤ 1`. -/
  P : HPolytope (Vec ℝ h)

def ConZonotope.construct (C : ConZonotope α) : Set α :=
  {x | ∃ β : Fin C.h → ℝ, (∀ j, |β j| ≤ 1) ∧ β ∈ C.P.construct
        ∧ x = C.c + ∑ j, β j • C.G j}

end CORALean.Real
