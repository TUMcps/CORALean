module

public import CORALean.ContSet.Polygon.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# A polygon is empty iff no piece has a vertex

Exactly: a polytope is empty iff it has no vertex.

## Inputs
* `P` – polygon

## Hypotheses
* none

## Conclusion
* A polygon is empty iff no piece has a vertex
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Polygon.aux_construct_eq_empty_iff (p : VPolytope (Vec ℝ 2)) : -- --- CONCL ---
    VPolytope.construct p = ∅ ↔ p.k = 0 := by -- --- PROOF ---
  constructor
  · intro h
    by_contra hk
    have := p.vertex_mem ⟨0, Nat.pos_of_ne_zero hk⟩
    rw [h] at this
    exact this
  · intro hk
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨β, -, hsum, -⟩
    have : IsEmpty (Fin p.k) := ⟨fun j => by have := j.2; omega⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.representsaEmptySet_iff (P : Polygon) : -- --- CONCL ---
    Polygon.representsaEmptySet P = true ↔ ContSet.construct P = ∅ := by -- --- PROOF ---
  simp only [Polygon.representsaEmptySet, List.all_eq_true, beq_iff_eq,
    Set.eq_empty_iff_forall_notMem, SetUnion.mem_construct, not_exists, not_and]
  constructor
  · intro h x p hp hx
    have := (Polygon.aux_construct_eq_empty_iff p).mpr (h p hp)
    have hx' : x ∈ VPolytope.construct p := hx
    rw [this] at hx'
    exact hx'
  · intro h p hp
    refine (Polygon.aux_construct_eq_empty_iff p).mp ?_
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact h x p hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
