module

public import CORALean.ContSet.ConPolyZono.Real.Operations.OfPoint

@[expose] public section

/-!
# A generator-free constrained polynomial zonotope contains its own centre

`ofPoint v` states its own `p`, `h`, `q` and `m`, that count only up to
unfolding, so both sums and the empty constraint system each need unfolding
to be seen as vacuous.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mem_ofPoint (v : α) : v ∈ (ConPolyZono.ofPoint v).construct := by
  refine ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun j => j.elim0, fun i => i.elim0, ?_⟩
  show v = v + ∑ i : Fin 0, PolyZonotope.monomial Fin.elim0 Fin.elim0 i • Fin.elim0 i
        + ∑ j : Fin 0, Fin.elim0 j • Fin.elim0 j
  rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, add_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
