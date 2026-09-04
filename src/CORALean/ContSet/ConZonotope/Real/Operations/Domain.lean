import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.domain`

The coefficients the representation admits, as one polytope: the unit box a
zonotope ranges over, intersected with what `P` adds.

The box is kept outside `P` in the structure, so that `zonotope` is an enclosure
whatever `P` says; this is where the two are put back together, and it is what
lets a constrained zonotope be read as an affine image of a polytope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.domain (C : ConZonotope α) : HPolytope (Vec ℝ C.h) :=
  (HPolytope.unitBox C.h).and C.P

omit [AddCommGroup α] [Module ℝ α] in
theorem ConZonotope.mem_domain_iff {C : ConZonotope α} {β : Vec ℝ C.h} :
    β ∈ C.domain.construct ↔ (∀ j, |β j| ≤ 1) ∧ β ∈ C.P.construct := by
  have hand : β ∈ C.domain.construct ↔ β ∈ (HPolytope.unitBox C.h).construct
      ∧ β ∈ C.P.construct := HPolytope.mem_and_iff
  rw [hand, HPolytope.mem_unitBox_iff]

end CORALean.Real
