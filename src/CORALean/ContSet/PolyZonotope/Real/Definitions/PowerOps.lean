module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The arithmetic the powers of a polynomial zonotope are computed in

CORA's `evaluatePolyZonotopeNeuron` multiplies and adds the generators of one neuron and doubles
and halves some of them (`calcSquared`). `PolyZonotope.evalPowersList` is written once over these
five operations, so the same definition runs over ℝ (`PowerOps.real`, the exact powers) and over
midpoint-radius floats (`PolyZonotope.midRadOps`, CORA's double arithmetic with its rounding
bounded), and `PolyZonotope.evalPowersList_rel` carries any relation the operations keep from the
inputs to the result.
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- Addition, multiplication and the constants `0`, `2` and `1/2` of a scalar the powers are
computed in. -/
structure PowerOps (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  two : α
  half : α

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
