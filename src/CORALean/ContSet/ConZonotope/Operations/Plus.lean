import CORALean.ContSet.ConZonotope.ConZonotope

/-!
# `ConZonotope.plus`

CORA's `@conZonotope/plus`: centres add and generators concatenate, as for a
zonotope, and the constraint block goes block diagonal so that each half of the
coefficient vector answers only to its own constraints.

The block is built row by row rather than with `Matrix.fromBlocks`, whose index
type is a sum where the field's is a `Fin`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.plus (C₁ C₂ : ConZonotope α) : ConZonotope α where
  h := C₁.h + C₂.h
  q := C₁.q + C₂.q
  c := C₁.c + C₂.c
  G := Fin.append C₁.G C₂.G
  A := Fin.append (fun i => Fin.append (C₁.A i) 0) fun i => Fin.append 0 (C₂.A i)
  b := Fin.append C₁.b C₂.b

end CORALean.Real
