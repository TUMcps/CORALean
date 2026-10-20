module

public import CORALean.ContSet.ConPolyZono.Real.Operations.RepresentsaPoint

@[expose] public section

/-!
# A constrained polynomial zonotope without generators lies in its center

With no generator column the points are `c` or nothing: the constraints can only remove it. CORA
answers `true` and returns `S = c` without looking at them, so for an infeasible constraint
system it names a point for the empty set.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* `h` – the test returns true

## Conclusion
* the set lies in the singleton of its center
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.construct_subset_of_representsa_point (cPZ : ConPolyZono α)
    (h : cPZ.representsa_point = true) : cPZ.construct ⊆ {cPZ.c} := by -- --- PROOF ---
  simp only [ConPolyZono.representsa_point, Bool.and_eq_true, beq_iff_eq] at h
  rintro _ ⟨a, β, -, -, -, rfl⟩
  -- both sums run over `Fin 0`
  have h1 : IsEmpty (Fin cPZ.h) := ⟨fun j => by have := j.2; omega⟩
  have h2 : IsEmpty (Fin cPZ.qI) := ⟨fun j => by have := j.2; omega⟩
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
