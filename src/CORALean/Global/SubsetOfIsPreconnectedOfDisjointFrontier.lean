module

public import Mathlib.Topology.Connected.Basic

@[expose] public section

/-!
# A connected set missing a boundary enclosure and meeting the set is inside it

[1, Thm. 1], which [1] takes from Chen, Sankaranarayanan and Ábrahám (FMCAD 2014, Sec. 3):
`B ⊇ ∂R`, a connected `C` with `C ∩ B = ∅` and `C ∩ R ≠ ∅` gives `C ⊆ R`. Nothing about `R` is
used — not closedness, not that it is a reachable set — and preconnected is enough: `C` misses
the frontier, so it splits into its parts in the interior and in the exterior of `R`, both
open, and the point of `C ∩ R` lies in the first.

## Inputs
* `C` – connected set
* `B` – boundary enclosure
* `R` – set

## Hypotheses
* `hB` – the enclosure contains the set's frontier
* `hC` – the connected set is preconnected
* `hCB` – the connected set misses the enclosure
* `hCR` – the connected set meets the set

## Conclusion
* the connected set lies in the set

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {X : Type*} [TopologicalSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: `∂R ⊆ B`, `C` preconnected, `C ∩ B = ∅` and `C ∩ R ≠ ∅` give `C ⊆ R`. -/
theorem subset_of_isPreconnected_of_disjoint_frontier {C B R : Set X} (hB : frontier R ⊆ B)
    (hC : IsPreconnected C) (hCB : C ∩ B = ∅) (hCR : (C ∩ R).Nonempty) : -- --- CONCL ---
    C ⊆ R := by -- --- PROOF ---
  -- a point of `C` in the closure of `R` is not on the frontier, so it is interior
  have hint : ∀ x ∈ C, x ∈ closure R → x ∈ interior R := fun x hx hcl => by
    by_contra hni
    exact (eq_empty_iff_forall_notMem.mp hCB) x ⟨hx, hB ⟨hcl, hni⟩⟩
  obtain ⟨x, hxC, hxR⟩ := hCR
  have hsub : C ⊆ interior R :=
    hC.subset_of_closure_inter_subset isOpen_interior
      ⟨x, hxC, hint x hxC (subset_closure hxR)⟩
      fun y hy => hint y hy.2 (closure_mono interior_subset hy.1)
  exact hsub.trans interior_subset

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
