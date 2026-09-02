import CORALean.ContSet.HPolytope.Operations.OfMat
import CORALean.ContSet.HPolytope.Operations.UnitBox
import CORALean.ContSet.HPolytope.Theorems.AndExact
import CORALean.ContSet.Zonotope.Real.Zonotope

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

/-- The same membership read coordinatewise, which is the form the operations
that need coordinates are stated in. -/
theorem ConZonotope.mem_construct_iff {n : ℕ} {C : ConZonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ C.construct ↔ ∃ β : Fin C.h → ℝ, (∀ j, |β j| ≤ 1) ∧ C.A *ᵥ β = C.b
      ∧ ∀ i, x i = C.c i + ∑ j, C.G j i * β j := by
  constructor
  · rintro ⟨β, hβ, hA, rfl⟩
    exact ⟨β, hβ, hA, Entrywise.add_sum_smul_apply C.c C.G β⟩
  · rintro ⟨β, hβ, hA, hx⟩
    exact ⟨β, hβ, hA,
      funext fun i => (hx i).trans (Entrywise.add_sum_smul_apply C.c C.G β i).symm⟩

/-- The coefficients the representation admits, as a polytope. -/
def ConZonotope.domain (C : ConZonotope α) : HPolytope (Vec ℝ C.h) :=
  (HPolytope.unitBox C.h).and (HPolytope.eqs C.A C.b)

omit [AddCommGroup α] [Module ℝ α] in
theorem ConZonotope.mem_domain_iff {C : ConZonotope α} {β : Vec ℝ C.h} :
    β ∈ C.domain.construct ↔ (∀ j, |β j| ≤ 1) ∧ C.A *ᵥ β = C.b := by
  have hand : β ∈ C.domain.construct ↔ β ∈ (HPolytope.unitBox C.h).construct
      ∧ β ∈ (HPolytope.eqs C.A C.b).construct := HPolytope.mem_and_iff
  rw [hand, HPolytope.mem_unitBox_iff, HPolytope.mem_eqs_iff, funext_iff]

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
