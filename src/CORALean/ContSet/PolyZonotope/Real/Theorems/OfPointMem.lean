module

public import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# A generator-free polynomial zonotope contains its own centre

`ofPoint v` states its own `p`, `h` and `q`, that count only up to unfolding,
so both sums need a `show`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mem_ofPoint (v : α) : v ∈ (PolyZonotope.ofPoint v).construct := by
  refine ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun j => j.elim0, ?_⟩
  show v = v + ∑ i : Fin 0, PolyZonotope.monomial Fin.elim0 Fin.elim0 i • Fin.elim0 i
        + ∑ j : Fin 0, Fin.elim0 j • Fin.elim0 j
  rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, add_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
