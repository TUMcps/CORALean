import CORALean.ContSet.ConZonotope.Operations.Plus

/-!
# `ConZonotope.and`

CORA's `@conZonotope/and_`, and the reason the representation exists: zonotopes
are not closed under intersection and constrained zonotopes are, exactly.

The coefficient vectors of both are concatenated, the two constraint systems go
block diagonal as in `plus`, and one further row per coordinate demands that the
two points agree — `G₁ β₁ - G₂ β₂ = c₂ - c₁`. Only the first generator block is
then kept, the second having been pinned to it.

At `Vec` only: those rows read a generator coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def ConZonotope.and (C₁ C₂ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) where
  h := C₁.h + C₂.h
  q := C₁.q + C₂.q + n
  c := C₁.c
  G := Fin.append C₁.G 0
  A := Fin.append
        (Fin.append (fun i => Fin.append (C₁.A i) 0) fun i => Fin.append 0 (C₂.A i))
        fun i => Fin.append (fun j => C₁.G j i) fun j => -C₂.G j i
  b := Fin.append (Fin.append C₁.b C₂.b) fun i => C₂.c i - C₁.c i

end CORALean.Real
