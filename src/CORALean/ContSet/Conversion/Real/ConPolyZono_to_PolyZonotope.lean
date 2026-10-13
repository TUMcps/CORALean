module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# A constrained polynomial zonotope as a polynomial zonotope

CORA's `polyZonotope(conPolyZono)` in its cheapest form: drop the constraints
and keep everything else.

Enclosing, and what is lost is exactly the constraints — the factors, which the
equalities were confining to a subvariety of the cube, are freed to range over
the whole of it. That is a genuine loss and not a rounding: the result contains
the original set and is generally strictly larger, and no operation recovers the
information. In particular it is what an intersection has to be undone by, so a
sequence of intersections must stay in this representation to mean anything.

Nothing else changes. The generators, the exponent matrix and both counts are
carried over unread, which is why the proof is one line per direction and why
the conversion costs nothing to compute.

CORA also offers tighter enclosures that first eliminate constraints by solving
for a factor. Those are separate operations, not this one.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConPolyZono.polyZonotope (cPZ : ConPolyZono α) : PolyZonotope α where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.polyZonotope_contains (cPZ : ConPolyZono α) :
    cPZ.construct ⊆ cPZ.polyZonotope.construct := by
  rintro _ ⟨a, b, ha, hb, _, rfl⟩
  exact ⟨a, b, ha, hb, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
