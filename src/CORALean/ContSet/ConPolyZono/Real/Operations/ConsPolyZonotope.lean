module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.consPolyZonotope`

The constraint data read as a `PolyZonotope` over the constraint codomain
`Vec ℝ m`: CORA's `polyZonotope(-cPZ.b, cPZ.A, [], cPZ.EC, cPZ.id)` inside
`@conPolyZono/getSubset`, with the offset dropped rather than carried as `-b` —
`b` is an `Interval` here and is `getSubset`'s own field, untouched by the
substitution, so there is nothing to fold in and fold back out.

Not a set-level operation, the same way `toPolyZonotope` is not: what it is for
is arithmetic, applying a `PolyZonotope` operation to the constraint block and
reading the constraint value back off `A *ᵥ monomial EC a` via
`mulVec_eq_sum`.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraint data read as a `PolyZonotope` over `Vec ℝ m`. -/
def ConPolyZono.consPolyZonotope {α : Type} (cPZ : ConPolyZono α) :
    PolyZonotope (Vec ℝ cPZ.m) where
  p := cPZ.p
  h := cPZ.s
  q := 0
  c := 0
  G := ConPolyZono.consCol cPZ.A
  E := cPZ.EC
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
