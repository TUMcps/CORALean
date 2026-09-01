import CORALean.ContSet.Polytope.API
import CORALean.ContSet.Zonotope.Real.API

/-!
# Constrained zonotopes: the representation

CORA's `conZonotope`, with the same fields: a zonotope's centre and generators
together with `A β = b`, restricting which coefficients are admissible.

The admissible coefficients are exactly a polytope — the unit box a zonotope
ranges over, intersected with the constraints — and `domain` names it. That is
what a constrained zonotope shares with `conPolyZono`, and why the halfspace
representation is developed before either.

Over any real module, as a zonotope is: the constraints live on the coefficient
space `Vec ℝ h`, whatever the generators point into.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure ConZonotope (α : Type) where
  h : ℕ
  q : ℕ
  c : α
  G : Fin h → α
  A : Mat ℝ q h
  b : Vec ℝ q

def ConZonotope.construct (C : ConZonotope α) : Set α :=
  {x | ∃ β : Fin C.h → ℝ, (∀ j, |β j| ≤ 1) ∧ C.A *ᵥ β = C.b ∧ x = C.c + ∑ j, β j • C.G j}

/-- The coefficients the representation admits, as a polytope. -/
def ConZonotope.domain (C : ConZonotope α) : Polytope (Vec ℝ C.h) :=
  (Polytope.unitBox C.h).and (Polytope.eqs C.A C.b)

omit [AddCommGroup α] [Module ℝ α] in
theorem ConZonotope.mem_domain_iff {C : ConZonotope α} {β : Vec ℝ C.h} :
    β ∈ C.domain.construct ↔ (∀ j, |β j| ≤ 1) ∧ C.A *ᵥ β = C.b := by
  have hand : β ∈ C.domain.construct ↔ β ∈ (Polytope.unitBox C.h).construct
      ∧ β ∈ (Polytope.eqs C.A C.b).construct := Polytope.mem_and_iff
  rw [hand, Polytope.mem_unitBox_iff, Polytope.mem_eqs_iff, funext_iff]

/-- A constrained zonotope is the zonotope's affine map applied to a polytope
rather than to a box. Every guarantee below is one of the two halves of this. -/
theorem ConZonotope.construct_eq_image (C : ConZonotope α) :
    C.construct = (fun β : Vec ℝ C.h => C.c + ∑ j, β j • C.G j) '' C.domain.construct := by
  ext x
  constructor
  · rintro ⟨β, hβ, hA, rfl⟩
    exact ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hβ, hA⟩, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨hbox, hA⟩ := ConZonotope.mem_domain_iff.mp hβ
    exact ⟨β, hbox, hA, rfl⟩

end CORALean.Real
