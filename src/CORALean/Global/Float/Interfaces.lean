module

public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# What a floating-point scalar offers and promises

`FloatOps` is the arithmetic a machine float offers, with no claim about what it computes.
`SoundFloatArithmetic` says its rounding directions are honest through a total `toReal` into ℝ, for
any format and for ℝ itself; not IEEE 754, and overflow is assumed away. The two are separate so
the layer stays executable. `RealImage` lifts the reading to an ambient type. `ToRat` decodes a
scalar exactly into ℚ, which ℝ cannot, for decisions the rounded operations cannot make, and
`isNaN` tells a NaN apart. `Floats 𝕋 α` lists the floats a value stores, for `noNaN`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

-- Import guards (CONTRIBUTING, "Import guards and layering"): what must stay out of the closure.

-- Measure theory, whose import closure is larger than this whole layer.
assert_not_exists MeasureTheory.Measure
-- Probability, which sits on top of measure theory.
assert_not_exists ProbabilityTheory.IndepFun
-- Determinants and the spectral theory built on them.
assert_not_exists Matrix.det
-- The analytic special functions; exact enclosures of them belong higher up.
assert_not_exists Real.exp
-- Calculus, which only the dynamics layers need.
assert_not_exists HasDerivAt
-- Inner-product geometry; the sup norm is what this layer uses.
assert_not_exists InnerProductSpace
-- The abstract set class sits above this file.
assert_not_imported CORALean.ContSet.ContSet.Interfaces
-- A concrete representation sits above this file.
assert_not_imported CORALean.ContSet.Interval.Real.Interval

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The operations a machine float offers: each rounding direction, and the exact ones. -/
class FloatOps (𝕋 : Type) where
  zero : 𝕋
  /-- Every format has it exactly, and a constraint matrix cannot name a
  coordinate without it. -/
  one : 𝕋
  /-- Sign is a bit, so negation needs no direction. -/
  neg : 𝕋 → 𝕋
  addUp : 𝕋 → 𝕋 → 𝕋
  addDown : 𝕋 → 𝕋 → 𝕋
  mulUp : 𝕋 → 𝕋 → 𝕋
  mulDown : 𝕋 → 𝕋 → 𝕋
  /-- Constrained only for a positive divisor, which costs nothing: `neg` is
  exact, so a caller dividing by a negative `b` negates both arguments. -/
  divUp : 𝕋 → 𝕋 → 𝕋
  divDown : 𝕋 → 𝕋 → 𝕋
  /-- Exact, like `neg`: choosing between two floats invents no digits. -/
  minimum : 𝕋 → 𝕋 → 𝕋
  maximum : 𝕋 → 𝕋 → 𝕋
  /-- `SoundFloatArithmetic` constrains a `true` answer only: that is what a
  generator ranking spends, and what lets a caller elsewhere discharge a bound
  hypothesis it already suspects holds. -/
  le : 𝕋 → 𝕋 → Bool
  /-- Exact in a binary format, where halving only moves the exponent. -/
  half : 𝕋 → 𝕋

open FloatOps

/-- That `FloatOps` rounds in the direction its name claims, read through `toReal`. -/
class SoundFloatArithmetic (𝕋 : Type) [FloatOps 𝕋] where
  toReal : 𝕋 → ℝ
  toReal_neg (a : 𝕋) : toReal (neg a) = -toReal a
  toReal_zero : toReal (zero : 𝕋) = 0
  toReal_one : toReal (one : 𝕋) = 1
  add_le_addUp (a b : 𝕋) : toReal a + toReal b ≤ toReal (addUp a b)
  addDown_le_add (a b : 𝕋) : toReal (addDown a b) ≤ toReal a + toReal b
  mul_le_mulUp (a b : 𝕋) : toReal a * toReal b ≤ toReal (mulUp a b)
  mulDown_le_mul (a b : 𝕋) : toReal (mulDown a b) ≤ toReal a * toReal b
  /-- The one partial guarantee: a divisor of zero bounds nothing, and a
  negative one is the caller's own negation away, `neg` being exact. -/
  div_le_divUp (a b : 𝕋) (hb : 0 < toReal b) : toReal a / toReal b ≤ toReal (divUp a b)
  divDown_le_div (a b : 𝕋) (hb : 0 < toReal b) : toReal (divDown a b) ≤ toReal a / toReal b
  toReal_minimum (a b : 𝕋) : toReal (minimum a b) = min (toReal a) (toReal b)
  toReal_maximum (a b : 𝕋) : toReal (maximum a b) = max (toReal a) (toReal b)
  /-- One direction only, see the module docstring for why. -/
  toReal_le_of_le {a b : 𝕋} (h : le a b = true) : toReal a ≤ toReal b
  toReal_half (a : 𝕋) : toReal (half a) = toReal a / 2

/-- The real ambient type a stored one denotes, and the reading: a vector of `𝕋`
reads as a vector of ℝ, a matrix as a matrix. -/
class RealImage (α : Type) (β : outParam Type) where
  realImage : α → β

/-- An exact, computable decoding into ℚ, agreeing with `toReal`. -/
class ToRat (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] where
  toRat : 𝕋 → ℚ
  toReal_toRat (x : 𝕋) : ((toRat x : ℚ) : ℝ) = SoundFloatArithmetic.toReal x
  /-- Native `Float.isNaN`; `false` at a format with no NaN. A NaN's `toRat` is a
  number like another, so this is the only way to tell it apart. -/
  isNaN : 𝕋 → Bool

/-- The scalars of type `𝕋` a value of type `α` stores, every one of them: a set is
reported only if none of these is a NaN. -/
class Floats (𝕋 : Type) (α : Type) where
  floats : α → List 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
