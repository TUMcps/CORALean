module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# A planar vertex description is the union of its vertex triangles

Carathéodory's theorem in the plane: a point of the hull of finitely many points lies in the hull
of at most three of them, so the hull is the union over all triples `(a, b, c)` of vertices of the
triangle they span (a degenerate one, a segment or a point, when two coincide). The triangles
overlap; this is a cover of the piece, not a partition.

## Inputs
* `p` – V-polytope

## Hypotheses
* none

## Conclusion
* A planar vertex description is the union of its vertex triangles
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_eq_iUnion_triples (p : VPolytope (Vec ℝ 2)) : -- --- CONCL ---
    p.construct = ⋃ (a : Fin p.k) (b : Fin p.k) (c : Fin p.k),
      (⟨3, ![p.V a, p.V b, p.V c]⟩ : VPolytope (Vec ℝ 2)).construct := by -- --- PROOF ---
  ext x
  simp only [Set.mem_iUnion, VPolytope.construct_eq_convexHull]
  constructor
  · intro hx
    rw [convexHull_eq_union] at hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨t, ht, hind, hxt⟩ := hx
    -- an affinely independent finset in the plane has at most three points
    have hcard : t.card ≤ 3 := by
      have h := hind.card_le_finrank_succ
      have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Vec ℝ 2))) ≤ 2 := by
        refine (Submodule.finrank_le _).trans ?_
        simp
      rw [Fintype.card_coe] at h
      exact h.trans (Nat.add_le_add_right h2 1)
    -- so it sits inside the hull of three vertices
    have hmem : ∀ y ∈ t, ∃ a : Fin p.k, p.V a = y := fun y hy => ht hy
    rcases (by omega : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 ∨ t.card = 3) with h | h | h | h
    · -- no points: the hull is empty
      rw [Finset.card_eq_zero] at h
      subst h
      simp at hxt
    · -- one point: the triple repeats it
      obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp h
      obtain ⟨a, rfl⟩ := hmem y (Finset.mem_singleton_self y)
      refine ⟨a, a, a, convexHull_mono ?_ hxt⟩
      intro z hz
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hz
      exact ⟨0, hz.symm⟩
    · -- two points: the triple repeats the second
      obtain ⟨y, z, -, rfl⟩ := Finset.card_eq_two.mp h
      obtain ⟨a, rfl⟩ := hmem y (by simp)
      obtain ⟨b, rfl⟩ := hmem z (by simp)
      refine ⟨a, b, b, convexHull_mono ?_ hxt⟩
      intro w hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · -- three points: the triple is the set
      obtain ⟨y, z, w, -, -, -, rfl⟩ := Finset.card_eq_three.mp h
      obtain ⟨a, rfl⟩ := hmem y (by simp)
      obtain ⟨b, rfl⟩ := hmem z (by simp)
      obtain ⟨c, rfl⟩ := hmem w (by simp)
      refine ⟨a, b, c, convexHull_mono ?_ hxt⟩
      intro v hv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · rintro ⟨a, b, c, hx⟩
    refine convexHull_mono ?_ hx
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩
    · exact ⟨c, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
