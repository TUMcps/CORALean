import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# A polynomial zonotope as a constrained one

Exact, and the cleanest check on the definition: keep every field and add no
constraints. With `m = 0` the constraint quantifies over an empty index, so
every factor vector satisfies it and the two sets are the same one, generator
for generator.

Read the other way, a constrained polynomial zonotope is a polynomial zonotope
exactly when its constraint system says nothing — which is what makes
`ConPolyZono` a conservative extension rather than a different representation.

The empty system is `A = 0` at `Fin 0 × Fin 0` rather than an empty list of
rows over the original constraint generators: with no rows there is nothing for
columns to be, and the exponent matrix is `Fin.elim0` per factor for the same
reason.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.conPolyZono (PZ : PolyZonotope α) : ConPolyZono α where
  p := PZ.p
  h := PZ.h
  q := PZ.q
  m := 0
  s := 0
  c := PZ.c
  G := PZ.G
  E := PZ.E
  GI := PZ.GI
  A := 0
  b := Interval.point 0
  EC := fun _ => Fin.elim0


-- =======================================  MAIN THEOREM  ======================================= --

-- with no constraint rows the system is vacuous, so both inclusions are the identity
theorem PolyZonotope.conPolyZono_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.conPolyZono.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, b, ha, hb, fun i => i.elim0, rfl⟩
  · rintro _ ⟨a, b, ha, hb, _, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
