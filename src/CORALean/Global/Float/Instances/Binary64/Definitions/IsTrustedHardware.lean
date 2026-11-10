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
`Float`'s own operations and about the decoding `toReal` defines; `Axioms` assumes it once. Each
field is true of the hardware wherever its result is a number. Every rounded operation returns NaN
outside the normal range (`stepUp`, `step_inRange`), and `toReal` decodes a NaN, whose bits Lean
reports as `0x7FF8000000000000`, as `1.5 * 2 ^ 1024`, which is where fields fail. The class asks
them everywhere, which no finite format can meet: the bundle is unsatisfiable
(`Theorems/NotIsTrustedHardware.lean`), and no model of binary64 could discharge it. README, "The
trust base", says what a run at `Float` rests on instead.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       22-September-2026
-- Last update:   10-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- ========================================  MAIN TYPE  ========================================= --

/-- What `SoundFloatArithmetic` asks of `Float`, for every input. FALSE as stated: no type whose
`toReal` takes finitely many values satisfies it (`not_isTrustedHardware`). Each field is true of
IEEE 754 binary64 except where its docstring says, and there a NaN is in its conclusion. -/
structure IsTrustedHardware : Prop where
  /-- True at every number and infinity: the sign bit flips and nothing else. False at a NaN,
  whose negation decodes to the same `1.5 * 2 ^ 1024`. -/
  toReal_neg : ∀ a : Float, toReal (-a) = -toReal a
  /-- True where neither is NaN, `±∞` included, the decoding being monotone; false where one is,
  as `minimum` then returns a NaN. -/
  toReal_min : ∀ a b : Float, toReal (minimum a b) = min (toReal a) (toReal b)
  /-- True everywhere: where one is NaN, so is the result, whose `1.5 * 2 ^ 1024` is above every
  other decoded value, Lean reporting every NaN by the same bits (as `hardwarecheck` finds). -/
  toReal_max : ∀ a b : Float, toReal (maximum a b) = max (toReal a) (toReal b)
  /-- True everywhere: a comparison with a NaN is `false`, and `±∞` decode to `±2 ^ 1024`,
  beyond every finite value. One direction only, which is all the class asks. -/
  toReal_le_of_le : ∀ a b : Float, a ≤ b → toReal a ≤ toReal b
  /-- True: the literal's bits are `0`. The kernel cannot evaluate `Float.toBits`, so this is
  trusted rather than computed. -/
  toReal_zero : toReal 0.0 = 0
  /-- True: the literal's bits are `0x3FF0000000000000`; trusted for the same reason. -/
  toReal_one : toReal 1.0 = 1
  /-- True where `a / 2` is zero or normal: only the exponent moves. False elsewhere, where
  `half` is NaN: a subnormal or non-finite result, or a NaN input. -/
  toReal_half : ∀ a : Float, toReal (half a) = toReal a / 2
  /-- True where the result is a number: `nextUp` of the nearest float is above the exact sum.
  False where it is a NaN and the exact sum exceeds `1.5 * 2 ^ 1024`, as near overflow. -/
  add_le_addUp : ∀ a b : Float, toReal a + toReal b ≤ toReal (addUp a b)
  /-- As `add_le_addUp`, of the product: false where it overflows past `1.5 * 2 ^ 1024`. -/
  mul_le_mulUp : ∀ a b : Float, toReal a * toReal b ≤ toReal (mulUp a b)
  /-- As `add_le_addUp`, of the quotient, for a positive divisor only: at zero there is no bound
  to state, and a negative divisor is the caller's own negation away. -/
  div_le_divUp : ∀ a b : Float, 0 < toReal b → toReal a / toReal b ≤ toReal (divUp a b)

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
