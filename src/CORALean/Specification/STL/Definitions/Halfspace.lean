module

public import CORALean.Specification.STL.Definitions.Pform
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-!
# Halfspace predicates and disjunctive normal form

[1, Sec. 5]: the atoms `aᵀx ∼ b`, `∼ ∈ {<, ≤, >, ≥}`, here `f x ∼ b` for a linear functional `f`
of a real vector space; a `Halfspace` is one with `∼ ∈ {<, ≤}`, and a `Dnf` a disjunction of
conjunctions of them: the polytopes `poly(c₁,…,c_k,d₁,…,d_k)` of the paper, open or closed face by
face.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

/-- A halfspace predicate: a linear functional bounded by `b`, strictly or not. -/
structure STL.Halfspace (α : Type) [AddCommGroup α] [Module ℝ α] where
  f : α →ₗ[ℝ] ℝ
  b : ℝ
  strict : Bool

/-- `f x < b` for a strict halfspace, `f x ≤ b` otherwise. -/
def STL.Halfspace.Holds (h : STL.Halfspace α) (x : α) : Prop :=
  if h.strict then h.f x < h.b else h.f x ≤ h.b

/-- A disjunction of conjunctions of halfspaces holds of `x`: `x ∈ ⋃ᵢ polyᵢ`. -/
def STL.Dnf.Holds (dnf : List (List (STL.Halfspace α))) (x : α) : Prop :=
  ∃ cl ∈ dnf, ∀ h ∈ cl, h.Holds x

/-- The four relations of an atom `f x ∼ b`. -/
inductive STL.Rel
  | lt
  | le
  | gt
  | ge

/-- `u ∼ v`. -/
def STL.Rel.Holds : STL.Rel → ℝ → ℝ → Prop
  | .lt, u, v => u < v
  | .le, u, v => u ≤ v
  | .gt, u, v => u > v
  | .ge, u, v => u ≥ v

/-- Every atom of `ϱ` is a halfspace predicate `x ↦ f x ∼ b`. -/
def Pform.IsHalfspaceForm : Pform α → Prop
  | .atom p => ∃ (f : α →ₗ[ℝ] ℝ) (b : ℝ) (r : STL.Rel), p = fun x => r.Holds (f x) b
  | .not ϱ => ϱ.IsHalfspaceForm
  | .or ϱ₁ ϱ₂ => ϱ₁.IsHalfspaceForm ∧ ϱ₂.IsHalfspaceForm


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
