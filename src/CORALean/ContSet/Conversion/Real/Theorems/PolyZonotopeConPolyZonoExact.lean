module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Interval.Real.Theorems.Basic

@[expose] public section

/-!
# A polynomial zonotope as a constrained one

Exact, and the cleanest check on the definition: keep every field and add no constraints. With
`m = 0` the constraint quantifies over an empty index, so every factor vector satisfies it and the
two sets are the same one, generator for generator. Read the other way, a constrained polynomial
zonotope is a polynomial zonotope exactly when its constraint system says nothing, which makes
`ConPolyZono` a conservative extension rather than a different representation. The empty system is
`A = 0` at `Fin 0 × Fin 0`, with nothing for columns to be, and the exponent matrix is `Fin.elim0`
per factor.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* set equals its constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- with no constraint rows the system is vacuous, so both inclusions are the identity
theorem PolyZonotope.conPolyZono_exact (pZ : PolyZonotope α) :
    pZ.construct = pZ.conPolyZono.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, b, hb, ⟨(Interval.mem_unit_iff a).mpr ha, fun i => i.elim0⟩, rfl⟩
  · rintro _ ⟨a, b, hb, hs, rfl⟩
    exact ⟨a, b, (Interval.mem_unit_iff a).mp hs.1, hb, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
