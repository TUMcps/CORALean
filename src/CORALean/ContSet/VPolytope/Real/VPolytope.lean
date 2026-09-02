import CORALean.ContSet.ContSet.ContSet

/-!
# Polytopes: the vertex representation

CORA's `polytope` with `isVRep` set: the convex hull of finitely many points,
written here as the convex combinations of them.

Over any real module, as a zonotope is, and for the same reason — nothing about
a convex combination mentions coordinates. Only the coefficient constraint
differs: `∑ βⱼ = 1` with `βⱼ ≥ 0` here, `|βⱼ| ≤ 1` there.

Zero vertices denote `∅`, no coefficient family over an empty index summing
to one.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure VPolytope (α : Type) where
  k : ℕ
  V : Fin k → α

def VPolytope.construct (P : VPolytope α) : Set α :=
  {x | ∃ β : Fin P.k → ℝ, (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 ∧ x = ∑ j, β j • P.V j}

/-- A vertex is a combination weighted entirely onto itself. -/
theorem VPolytope.vertex_mem (P : VPolytope α) (j : Fin P.k) : P.V j ∈ P.construct := by
  have hnn : ∀ l : Fin P.k, 0 ≤ (if l = j then (1:ℝ) else 0) := by
    intro l; split <;> [exact zero_le_one; exact le_rfl]
  have hsum : ∑ l : Fin P.k, (if l = j then (1:ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ j fun _ => (1:ℝ), if_pos (Finset.mem_univ j)]
  have hsmul : ∀ l : Fin P.k, (if l = j then (1:ℝ) else 0) • P.V l
      = if l = j then P.V l else 0 := by
    intro l; split <;> [rw [one_smul]; rw [zero_smul]]
  have hval : ∑ l, (if l = j then (1:ℝ) else 0) • P.V l = P.V j := by
    rw [Finset.sum_congr rfl fun l _ => hsmul l, Finset.sum_ite_eq' Finset.univ j P.V,
      if_pos (Finset.mem_univ j)]
  exact ⟨fun l => if l = j then 1 else 0, hnn, hsum, hval.symm⟩

/-- No vertices: there is no coefficient family over an empty index summing to
one, so this denotes `∅`. -/
def VPolytope.emptySet (α : Type) : VPolytope α := ⟨0, Fin.elim0⟩

theorem VPolytope.construct_emptySet : (VPolytope.emptySet α).construct = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, -, hsum, -⟩
  -- ascribed at the projection spelling of the count, which is `0` only by defeq
  have hz : ∑ j : Fin (VPolytope.emptySet α).k, β j = 0 := Fin.sum_univ_zero _
  rw [hz] at hsum
  linarith

/-- One vertex, which is the singleton. Composed with `plus` this is a
translation, so the representation needs no separate one. -/
def VPolytope.point (v : α) : VPolytope α := ⟨1, fun _ => v⟩

theorem VPolytope.construct_point (v : α) : (VPolytope.point v).construct = {v} := by
  ext x
  constructor
  · rintro ⟨β, -, hsum, rfl⟩
    refine Set.mem_singleton_iff.mpr ?_
    -- shown at `Fin 1`, the count's reduced spelling, so `Fin.sum_univ_one` matches
    have h1 : β (0 : Fin 1) = 1 := by
      rw [← hsum]
      exact (Fin.sum_univ_one (β : Fin 1 → ℝ)).symm
    show ∑ j : Fin 1, β j • v = v
    rw [Fin.sum_univ_one, h1, one_smul]
  · rintro rfl
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_, ?_⟩
    · show ∑ _j : Fin 1, (1:ℝ) = 1
      rw [Fin.sum_univ_one]
    · show x = ∑ _j : Fin 1, (1:ℝ) • x
      rw [Fin.sum_univ_one, one_smul]

end CORALean.Real
