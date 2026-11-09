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
`isNaN` tells a NaN apart. `ExactLe` is one such decision, the comparison of two scalars as reals
and MATLAB's `withinTol` of them, which every format with `ToRat` has and ℝ decides classically.
`Floats 𝕋 α` lists the floats a value stores, for `noNaN`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       16-August-2026
-- Last update:   07-November-2026
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

/-- The six elementary functions a format may compute itself: each one value, standing for the
lower and the upper bound alike (so `sinDown n a = sinUp n a = sin a`, the machine's). -/
structure ElemOverride (𝕋 : Type) where
  sin : 𝕋 → 𝕋
  cos : 𝕋 → 𝕋
  exp : 𝕋 → 𝕋
  log : 𝕋 → 𝕋
  tan : 𝕋 → 𝕋
  atan : 𝕋 → 𝕋

/-- A reference for the six elementary functions, over the reals; the standard one is in
`ElemOverride.lean`. Data only, so that the interface layer need not name `Real.sin`. -/
structure RealElem where
  sin : ℝ → ℝ
  cos : ℝ → ℝ
  exp : ℝ → ℝ
  log : ℝ → ℝ
  tan : ℝ → ℝ
  atan : ℝ → ℝ

/-- `e` computes `R`'s functions exactly, read through `toReal` (`log` where positive). -/
def ElemOverride.IsExact {𝕋 : Type} (toReal : 𝕋 → ℝ) (e : ElemOverride 𝕋) (R : RealElem) : Prop :=
  (∀ a, toReal (e.sin a) = R.sin (toReal a)) ∧ (∀ a, toReal (e.cos a) = R.cos (toReal a))
  ∧ (∀ a, toReal (e.exp a) = R.exp (toReal a))
  ∧ (∀ a, 0 < toReal a → toReal (e.log a) = R.log (toReal a))
  ∧ (∀ a, toReal (e.tan a) = R.tan (toReal a)) ∧ (∀ a, toReal (e.atan a) = R.atan (toReal a))

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
  /-- A strict comparison `a < b`: a `true` certifies it. By default `a` plus `2⁻⁶⁴`, rounded up, is
  at most `b`; a format that rounds to nearest overrides it, there `a + 2⁻⁶⁴ = a` above `2⁻¹¹`. -/
  ltStrict : 𝕋 → 𝕋 → Bool := fun a b => le (addUp a (half^[64] one)) b
  /-- A square root rounded up that the format computes itself, from `p` and the radicand. By
  default there is none and `sqrtUp` is the Newton iteration of `Sqrt.lean`; the round-to-nearest
  bench baseline supplies the machine's square root. `SoundFloatArithmetic` constrains it. -/
  sqrtUpOverride : Option (ℕ → 𝕋 → 𝕋) := none
  /-- The elementary functions the format computes itself, one value for both directions; none by
  default, then the bracketing algorithms of `SinCos.lean` and its siblings. See the module
  docstring. -/
  elemOverride : Option (ElemOverride 𝕋) := none

open FloatOps

/-- `ltStrict`'s default is strict, from `SoundFloatArithmetic`'s own fields passed one by one: an
instance that keeps the default proves its `toReal_lt_of_ltStrict` by this. -/
theorem toReal_lt_of_default_ltStrict {𝕋 : Type} [FloatOps 𝕋] (toReal : 𝕋 → ℝ)
    (toReal_one : toReal one = 1) (toReal_half : ∀ a : 𝕋, toReal (half a) = toReal a / 2)
    (add_le_addUp : ∀ a b : 𝕋, toReal a + toReal b ≤ toReal (addUp a b))
    (toReal_le_of_le : ∀ {a b : 𝕋}, le a b = true → toReal a ≤ toReal b) {a b : 𝕋}
    (h : le (addUp a (Nat.iterate half 64 one)) b = true) : -- --- CONCL ---
    toReal a < toReal b := by -- --- PROOF ---
  have hm : ∀ k : ℕ, 0 < toReal (Nat.iterate half k (one : 𝕋)) := by
    intro k
    induction k with
    | zero => rw [Function.iterate_zero_apply, toReal_one]; exact one_pos
    | succ k ih => rw [Function.iterate_succ_apply', toReal_half]; exact half_pos ih
  exact lt_of_lt_of_le (lt_add_of_pos_right _ (hm 64))
    (le_trans (add_le_addUp a _) (toReal_le_of_le h))

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
  /-- A `true` strict comparison is strict. A format that keeps `ltStrict`'s default gets this
  from `toReal_lt_of_default_ltStrict` and the fields above. -/
  toReal_lt_of_ltStrict {a b : 𝕋} (h : ltStrict a b = true) : toReal a < toReal b
  /-- A square root the format supplies is above the real one: above every nonnegative `r` whose
  square is at most the radicand, clamped at 0 as the Newton root is. Vacuous for the default,
  which has none (`by cases hf`); `sqrtUp` is then the Newton iteration, sound by `le_sqrtUp`. -/
  le_sqrtUpOverride {f : ℕ → 𝕋 → 𝕋} (hf : sqrtUpOverride = some f) (p : ℕ) (a : 𝕋) :
      ∀ r : ℝ, 0 ≤ r → r * r ≤ max (toReal a) 0 → r ≤ toReal (f p a)
  /-- A format's own elementary functions are exact at every reference `R` (`ElemOverride.lean`
  says why `R` is quantified); vacuous for the default, which has none. -/
  elemOverride_exact {e : ElemOverride 𝕋} (he : elemOverride = some e) (R : RealElem) :
      ElemOverride.IsExact toReal e R

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

/-- An exact comparison, which `FloatOps.le` is not: `le a b` decides `toReal a ≤ toReal b`, both
ways, for an algorithm that only orders stored values (`TimeOrder`); `withinTol tol a b` decides
MATLAB's `withinTol(a,b,tol)` on the reals as exactly. -/
class ExactLe (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] where
  le : 𝕋 → 𝕋 → Bool
  le_iff (a b : 𝕋) :
    le a b = true ↔ SoundFloatArithmetic.toReal a ≤ SoundFloatArithmetic.toReal b
  withinTol : 𝕋 → 𝕋 → 𝕋 → Bool
  withinTol_iff (tol a b : 𝕋) : withinTol tol a b = true ↔
    |SoundFloatArithmetic.toReal a - SoundFloatArithmetic.toReal b| ≤
        SoundFloatArithmetic.toReal tol ∨
      |SoundFloatArithmetic.toReal a - SoundFloatArithmetic.toReal b| ≤
        SoundFloatArithmetic.toReal tol *
          min |SoundFloatArithmetic.toReal a| |SoundFloatArithmetic.toReal b|

/-- The scalars of type `𝕋` a value of type `α` stores, every one of them: a set is
reported only if none of these is a NaN. -/
class Floats (𝕋 : Type) (α : Type) where
  floats : α → List 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
