module

public import CORALean.Global.Float.Instances.Binary64.Operations.AddUp
public import CORALean.Global.Float.Instances.Binary64.Operations.DivUp
public import CORALean.Global.Float.Instances.Binary64.Operations.Half
public import CORALean.Global.Float.Instances.Binary64.Operations.Basic
public import CORALean.Global.Float.Instances.Binary64.Operations.MulUp

@[expose] public section

/-!
# What "the hardware is trusted" says

One property with ten conjuncts: everything `SoundFloatArithmetic` asks of a scalar, stated about
`Float`'s own operations and about the decoding `toReal` defines. `Axioms` assumes this once, the
only assumption in the library. Bundled rather than left as ten separate assumptions so that the
trust is a single object: one name in every `#print axioms` that reaches `Float`, one place that
says what is trusted and on which runs, and one thing to discharge should a verified model of
binary64 ever arrive, at which point this backend becomes axiom-free with nothing else changing. The
price is resolution: `addDown_le_add` now names the bundle, as everything else does, though its
proof still names the assumptions it uses.
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- ========================================  MAIN TYPE  ========================================= --

/-- True of IEEE 754 binary64 while every value stays in its normal range. Not expressible
here, so stated unconditionally and false beyond it; the operations return NaN where a value
would leave the range, which makes such a run visible: see `Axioms`. -/
structure TrustedHardware : Prop where
  /-- Negation flips the sign bit and touches nothing else. -/
  toReal_neg : ∀ a : Float, toReal (-a) = -toReal a
  /-- Choosing between two floats invents no digits. -/
  toReal_min : ∀ a b : Float, toReal (minimum a b) = min (toReal a) (toReal b)
  /-- And neither does choosing the other one. -/
  toReal_max : ∀ a b : Float, toReal (maximum a b) = max (toReal a) (toReal b)
  /-- One direction only, which is all the class asks and all a NaN leaves
  true: every comparison against one is `false`. -/
  toReal_le_of_le : ∀ a b : Float, a ≤ b → toReal a ≤ toReal b
  /-- The kernel cannot evaluate `Float.toBits`, so what the literal `0.0`
  decodes to is trusted rather than computed. -/
  toReal_zero : toReal 0.0 = 0
  /-- And the same for `1.0`. -/
  toReal_one : toReal 1.0 = 1
  /-- Exact on a binary format, where halving moves the exponent alone — except
  at the bottom of the range, where the result is subnormal and `half` is NaN. -/
  toReal_half : ∀ a : Float, toReal (half a) = toReal a / 2
  /-- The machine's round-to-nearest sum, stepped one unit in the last place up,
  is at least the exact sum — true whenever that step lands on a normal float. -/
  add_le_addUp : ∀ a b : Float, toReal a + toReal b ≤ toReal (addUp a b)
  /-- The same of the product. -/
  mul_le_mulUp : ∀ a b : Float, toReal a * toReal b ≤ toReal (mulUp a b)
  /-- And of the quotient, for a positive divisor only: at zero there is no
  bound to state, and a negative divisor is the caller's own negation away. -/
  div_le_divUp : ∀ a b : Float, 0 < toReal b → toReal a / toReal b ≤ toReal (divUp a b)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
