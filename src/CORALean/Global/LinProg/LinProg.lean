import CORALean.Global.Tensor

/-!
# Bounds on a linear objective

Every operation that has to leave one set representation for another eventually
asks the same question: how far does this set reach in direction `c`? For a
polytope that question is a linear program, and this is the shape of its answer.

A `SupportBound` is a number together with the fact that no point of the set
exceeds it. It says nothing about where the number came from, which is exactly
the point: a simplex implementation may produce it and need not be trusted,
because the dual solution it returns *proves* the bound by weak duality, and it
is the proof that gets carried. Nothing here is axiomatised and nothing is
`sorry`; an unverified solver stays outside the trusted base by construction.

Stated over a `Set`, not a representation, so a bound transfers along the set
operations rather than along any particular description of them —
`Duality` says where bounds come from, `Composition` how they travel.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S T : Set α} {c : α →ₗ[ℝ] ℝ}

structure SupportBound (S : Set α) (c : α →ₗ[ℝ] ℝ) where
  val : ℝ
  le : ∀ x ∈ S, c x ≤ val

/-- A bound on the larger set bounds the smaller. -/
def SupportBound.mono (h : S ⊆ T) (u : SupportBound T c) : SupportBound S c :=
  ⟨u.val, fun x hx => u.le x (h hx)⟩

/-- A bound may always be loosened, which is what makes rounding it outward
sound. -/
def SupportBound.raise (u : SupportBound S c) {v : ℝ} (h : u.val ≤ v) : SupportBound S c :=
  ⟨v, fun x hx => le_trans (u.le x hx) h⟩

/-- Nothing to exceed, so any number will do. -/
def SupportBound.ofEmpty (v : ℝ) : SupportBound (∅ : Set α) c :=
  ⟨v, fun _ h => h.elim⟩

end CORALean
