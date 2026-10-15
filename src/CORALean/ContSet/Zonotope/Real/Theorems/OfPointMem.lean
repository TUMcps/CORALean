module

public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# A generator-free zonotope contains its own center

`ofPoint v` states its own `h`, that counts only up to unfolding, so the sum
needs a `show`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_ofPoint (v : α) : v ∈ (Zonotope.ofPoint v).construct := by
  refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
  show v = v + ∑ j : Fin 0, Fin.elim0 j • Fin.elim0 j
  rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
