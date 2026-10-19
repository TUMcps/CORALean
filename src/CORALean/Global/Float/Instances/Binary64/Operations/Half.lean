module

public import CORALean.Global.Float.Instances.Binary64.Binary64

@[expose] public section

/-!
# Halving

The one operation both directions agree on: `half` is `Axioms`' assumed equality, not a rounded
primitive. It holds while the result is normal, where only the exponent moves; a result below the
normal range would have lost a bit, so `aux_inRange` makes it NaN instead. The smallest subnormal is
the one such input whose half rounds to zero, which `aux_inRange` keeps: it is NaN here too (found
by `hardwarecheck`).
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       22-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `x` where it is finite and zero or normal, and NaN otherwise. Constants by their bits, which
compile to one load, where a literal such as `0.0` is `Float.ofScientific` again on every call. -/
def aux_inRange (x : Float) : Float :=
  if x.isFinite && (x == Float.ofBits 0 || Float.ofBits 0x0010000000000000 ≤ x.abs) then x
  else Float.ofBits 0x7FF8000000000000


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact where the result is normal, and NaN where it is not. `0.5` by its bits, see `aux_inRange`.
-/
def half (a : Float) : Float :=
  let r := a * Float.ofBits 0x3FE0000000000000
  -- a nonzero `a` whose half is zero has underflowed, as in `MulUp`; `0` and NaN by their bits
  if r == Float.ofBits 0 && a != Float.ofBits 0 then Float.ofBits 0x7FF8000000000000
  else aux_inRange r

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
