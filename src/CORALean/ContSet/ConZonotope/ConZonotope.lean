import CORALean.ContSet.HPolytope.Operations.Comap
import CORALean.ContSet.HPolytope.Operations.OfMat
import CORALean.ContSet.HPolytope.Operations.UnitBox
import CORALean.ContSet.HPolytope.Theorems.AndExact
import CORALean.ContSet.HPolytope.Theorems.Convex
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
-- Last update:   02-September-2026
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

/-- CORA's `conZonotope(c, G, A, b)`, whose constraints are an equality system. -/
def ConZonotope.ofMat {q h : ℕ} (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) :
    ConZonotope α :=
  ⟨h, c, G, HPolytope.eqs A b⟩

theorem ConZonotope.mem_ofMat_iff {q h : ℕ} {c : α} {G : Fin h → α} {A : Mat ℝ q h}
    {b : Vec ℝ q} {x : α} :
    x ∈ (ConZonotope.ofMat c G A b).construct ↔
      ∃ β : Fin h → ℝ, (∀ j, |β j| ≤ 1) ∧ (∀ i, (A *ᵥ β) i = b i)
        ∧ x = c + ∑ j, β j • G j :=
  ⟨fun ⟨β, hβ, hP, hx⟩ => ⟨β, hβ, HPolytope.mem_eqs_iff.mp hP, hx⟩,
   fun ⟨β, hβ, hA, hx⟩ => ⟨β, hβ, HPolytope.mem_eqs_iff.mpr hA, hx⟩⟩

/-- The coefficients the representation admits, as one polytope: the unit box a
zonotope ranges over, intersected with what `P` adds. -/
def ConZonotope.domain (C : ConZonotope α) : HPolytope (Vec ℝ C.h) :=
  (HPolytope.unitBox C.h).and C.P

omit [AddCommGroup α] [Module ℝ α] in
theorem ConZonotope.mem_domain_iff {C : ConZonotope α} {β : Vec ℝ C.h} :
    β ∈ C.domain.construct ↔ (∀ j, |β j| ≤ 1) ∧ β ∈ C.P.construct := by
  have hand : β ∈ C.domain.construct ↔ β ∈ (HPolytope.unitBox C.h).construct
      ∧ β ∈ C.P.construct := HPolytope.mem_and_iff
  rw [hand, HPolytope.mem_unitBox_iff]

/-- The same membership read coordinatewise, which is the form the operations
that need coordinates are stated in. -/
theorem ConZonotope.mem_construct_iff {n : ℕ} {C : ConZonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ C.construct ↔ ∃ β : Fin C.h → ℝ, (∀ j, |β j| ≤ 1) ∧ β ∈ C.P.construct
      ∧ ∀ i, x i = C.c i + ∑ j, C.G j i * β j := by
  constructor
  · rintro ⟨β, hβ, hP, rfl⟩
    exact ⟨β, hβ, hP, Entrywise.add_sum_smul_apply C.c C.G β⟩
  · rintro ⟨β, hβ, hP, hx⟩
    exact ⟨β, hβ, hP,
      funext fun i => (hx i).trans (Entrywise.add_sum_smul_apply C.c C.G β i).symm⟩

/-- A constrained zonotope is the zonotope's affine map applied to a polytope
rather than to a box. Every guarantee below is one of the two halves of this. -/
theorem ConZonotope.construct_eq_image (C : ConZonotope α) :
    C.construct = (fun β : Vec ℝ C.h => C.c + ∑ j, β j • C.G j) '' C.domain.construct := by
  ext x
  constructor
  · rintro ⟨β, hβ, hP, rfl⟩
    exact ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hβ, hP⟩, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨hbox, hP⟩ := ConZonotope.mem_domain_iff.mp hβ
    exact ⟨β, hbox, hP, rfl⟩

end CORALean.Real
