module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Interval.Real.Theorems.Basic

@[expose] public section

/-!
# A constrained polynomial zonotope as a polynomial zonotope

CORA's `polyZonotope(conPolyZono)` in its cheapest form: drop the constraints and keep everything
else. Enclosing, and what is lost is exactly the constraints: the factors, which the equalities were
confining to a subvariety of the cube, are freed to range over the whole of it. The result contains
the original set and is generally strictly larger, so a sequence of intersections must stay in this
representation to mean anything. The generators, the exponent matrix and both counts are carried
over unread. CORA also offers tighter enclosures that first eliminate constraints by solving for a
factor; those are separate operations, not this one.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its polynomial zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.polyZonotope_contains (cPZ : ConPolyZono α) :
    cPZ.construct ⊆ cPZ.polyZonotope.construct := by
  rintro _ ⟨a, b, hb, hs, rfl⟩
  exact ⟨a, b, (Interval.mem_unit_iff a).mp (cPZ.cons_dom ▸ hs.1), hb, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
