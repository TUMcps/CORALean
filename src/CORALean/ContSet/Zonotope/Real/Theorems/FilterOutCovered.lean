module

public import CORALean.ContSet.Zonotope.Real.Operations.FilterOut
public import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-!
# A deleted cell is covered by the others

A cell with nonempty interior that `filterOut` deletes lies in the union of all the other cells,
the deleted ones included. A point of the cell outside that closed union would have a
neighbourhood outside it, and the cell, being the closure of its interior, meets that
neighbourhood in an open set, which is a remainder of nonempty interior.

Covered by *all* the others, not by the cells that are kept: `filterOut_pair` has two equal cells
delete each other.

Source: [1].

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.filterOut_covered (Zs : Fin m → Zonotope (Vec ℝ n)) (ind : Fin m)
    (hint : (interior (Zs ind).construct).Nonempty) (hout : ind ∉ Zonotope.filterOut Zs) :
    (Zs ind).construct ⊆ ⋃ j ∈ {j | j ≠ ind}, (Zs j).construct := by -- --- PROOF ---
  intro x hx
  by_contra hxU
  set U : Set (Vec ℝ n) := ⋃ j ∈ {j | j ≠ ind}, (Zs j).construct with hU
  have hUclosed : IsClosed U := by
    refine (Set.toFinite {j : Fin m | j ≠ ind}).isClosed_biUnion fun j _ => ?_
    exact Zonotope.isClosed_construct (Zs j)
  -- the cell is the closure of its interior
  have hcl : closure (interior (Zs ind).construct) = (Zs ind).construct := by
    rw [(Zonotope.convex_construct (Zs ind)).closure_interior_eq_closure_of_nonempty_interior hint,
      (Zonotope.isClosed_construct (Zs ind)).closure_eq]
  have hxcl : x ∈ closure (interior (Zs ind).construct) := by rw [hcl]; exact hx
  -- so the open set outside `U` meets the interior
  have hopen : IsOpen (interior (Zs ind).construct ∩ Uᶜ) :=
    isOpen_interior.inter hUclosed.isOpen_compl
  obtain ⟨y, hy⟩ : (interior (Zs ind).construct ∩ Uᶜ).Nonempty := by
    rw [mem_closure_iff] at hxcl
    obtain ⟨y, hyU, hyI⟩ := hxcl Uᶜ hUclosed.isOpen_compl hxU
    exact ⟨y, hyI, hyU⟩
  apply hout
  refine ⟨y, interior_maximal ?_ hopen hy⟩
  rintro z ⟨hz1, hz2⟩
  exact ⟨interior_subset hz1, hz2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
