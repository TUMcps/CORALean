module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# A generator-free, constraint-free constrained zonotope contains its center

`ofPoint v` states its own `h` and `P`, that count only up to unfolding, so
the coefficient carries a `show` before the sum and the constraint discharges
on no row at all — `HPolytope.fullspace` has none.

## Inputs
* `v` – point

## Hypotheses
* none

## Conclusion
* the point lies in its own constrained zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_ofPoint (v : α) : v ∈ (ConZonotope.ofPoint v).construct := by
  refine ⟨Fin.elim0, fun j => j.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
  show v = v + ∑ j : Fin 0, Fin.elim0 j • Fin.elim0 j
  rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
