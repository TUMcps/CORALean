module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Bounds on a linear objective

Every operation that has to leave one set representation for another asks how far this set reaches
in direction `c`; this is the shape of its answer. Bounds are produced by closed forms, by
composition (`Composition`), and by LP duality (`Global/LinProg/Duality`). A `SupportBound` is a
number together with the fact that no point of the set exceeds it, and says nothing about where the
number came from: a simplex implementation may produce it and need not be trusted, because the dual
solution it returns *proves* the bound by weak duality, and the proof is what gets carried. Stated
over a `Set`, not a representation, so a bound transfers along set operations. `SupportWitness` is
the dual: a value with a point attaining it; no `ofEmpty`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S T : Set α} {c : α →ₗ[ℝ] ℝ}


-- ========================================  MAIN TYPE  ========================================= --

/-- An upper bound `val` on the linear objective `c` over the set `S`. -/
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

/-- A point of `S` whose objective value is at least `val`: a lower bound of the supremum. -/
structure SupportWitness (S : Set α) (c : α →ₗ[ℝ] ℝ) where
  val : ℝ
  mem : ∃ x ∈ S, val ≤ c x

/-- A witness for `S` is a witness for any larger set — the opposite direction
from `SupportBound.mono`. -/
def SupportWitness.mono (h : S ⊆ T) (u : SupportWitness S c) : SupportWitness T c :=
  ⟨u.val, let ⟨x, hx, hv⟩ := u.mem; ⟨x, h hx, hv⟩⟩

/-- A witness may always be weakened downward, which is what makes rounding it
inward sound. -/
def SupportWitness.lower (u : SupportWitness S c) {v : ℝ} (h : v ≤ u.val) : SupportWitness S c :=
  ⟨v, let ⟨x, hx, hv⟩ := u.mem; ⟨x, hx, le_trans h hv⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
