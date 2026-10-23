module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The scalar a layer computes in, and the ambient types that have coordinates

`Scalar 𝕋` is a type whose matrices and vectors denote real ones: ℝ itself, or a machine scalar
read entrywise, which is what lets one guarantee cover both. `ExactScalar` adds a `0` and a `1`
that read back as the real ones, all a block matrix needs; `ExactAdd` is the law that a sum reads
as the real sum, which holds at ℝ and at no float format (#117, #40), and `NegScalar` the same for
negation, exact in every format. `Entrywise α ι` reads an ambient type coordinate by coordinate,
`Fin n` for a vector and `Fin m × Fin n` for a matrix, `entry` linear and injective.
`TimeOrder T` is what an algorithm on time stamps compares with: a linear order's own order, or a
float format's exact comparison, so that a signal stores the scalar its layer computes in.
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-August-2026
-- Last update:   23-October-2026
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
-- The entrywise lemmas sit above this file.
assert_not_imported CORALean.Global.Entrywise
-- The abstract set class sits above this file.
assert_not_imported CORALean.ContSet.ContSet.Interfaces
-- A concrete representation sits above this file.
assert_not_imported CORALean.ContSet.Interval.Real.Interval

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A type whose vectors and matrices read as real ones, entry by entry: ℝ itself, or a machine
scalar. -/
class Scalar (𝕋 : Type) where
  toRealMat {m n : ℕ} : Mat 𝕋 m n → Mat ℝ m n
  toRealVec {n : ℕ} : Vec 𝕋 n → Vec ℝ n
  toReal : 𝕋 → ℝ
  toRealMat_apply {m n : ℕ} (M : Mat 𝕋 m n) (i : Fin m) (j : Fin n) :
    toRealMat M i j = toReal (M i j)
  toRealVec_apply {n : ℕ} (v : Vec 𝕋 n) (i : Fin n) : toRealVec v i = toReal (v i)

/-- ℝ stores itself. -/
instance : Scalar ℝ where
  toRealMat M := M
  toRealVec v := v
  toReal := id
  toRealMat_apply _ _ _ := rfl
  toRealVec_apply _ _ := rfl

/-- The family of sets of real vectors, `(S := 𝒮)`: the denotations every representation's
`construct` lands in. -/
notation "𝒮" => fun n => Set (Vec ℝ n)

/-- True by `rfl`, but a proof about the real layer has to rewrite with it. -/
@[simp] theorem Scalar.toRealMat_real {m n : ℕ} (M : Mat ℝ m n) : toRealMat M = M := rfl

/-- True by `rfl`, but a proof about the real layer has to rewrite with it. -/
@[simp] theorem Scalar.toRealVec_real {n : ℕ} (v : Vec ℝ n) : toRealVec v = v := rfl

open Scalar

/-- A scalar with a `0` and a `1` that read back as the real ones. -/
class ExactScalar (𝕋 : Type) [Scalar 𝕋] extends Zero 𝕋, One 𝕋 where
  toReal_zero : toReal (0 : 𝕋) = 0
  toReal_one : toReal (1 : 𝕋) = 1

/-- `ℝ` reads itself back, entry by entry. -/
instance : ExactScalar ℝ where
  toReal_zero := rfl
  toReal_one := rfl

/-- A scalar whose `+` reads back as the real sum. -/
class ExactAdd (𝕋 : Type) [Scalar 𝕋] extends Add 𝕋 where
  toReal_add (a b : 𝕋) : toReal (a + b) = toReal a + toReal b

/-- `ℝ` adds exactly. -/
instance : ExactAdd ℝ where
  toReal_add _ _ := rfl

/-- A scalar whose `-` reads back as the real negation. -/
class NegScalar (𝕋 : Type) [Scalar 𝕋] [Neg 𝕋] where
  toReal_neg (a : 𝕋) : toReal (-a) = -toReal a

/-- `ℝ` negates itself. -/
instance : NegScalar ℝ where
  toReal_neg _ := rfl

/-- The comparisons an algorithm on time stamps branches on, with no law of their own: a linear
order's, or a float format's exact ones read through `toReal` (`ExactLe`). The order parents are
low-priority instances, so a type with an order of its own (`Float`) keeps it. -/
class TimeOrder (T : Type) extends LE T, LT T where
  /-- Two time stamps denote the same time. -/
  Eqv : T → T → Prop
  decLe : DecidableRel (· ≤ · : T → T → Prop)
  decLt : DecidableRel (· < · : T → T → Prop)
  decEqv : DecidableRel Eqv

attribute [instance low] TimeOrder.toLE TimeOrder.toLT
attribute [reducible, instance] TimeOrder.decLe TimeOrder.decLt TimeOrder.decEqv

/-- A linear order compares with its own order and equality. -/
instance {T : Type} [LinearOrder T] : TimeOrder T where
  Eqv a b := a = b
  decLe := inferInstance
  decLt := inferInstance
  decEqv := inferInstance

/-- At a linear order, `Eqv` is equality. -/
@[simp] theorem TimeOrder.eqv_iff_eq {T : Type} [LinearOrder T] (a b : T) :
    TimeOrder.Eqv a b ↔ a = b := Iff.rfl

/-- An ambient type read coordinate by coordinate, over the index set `ι`, with `entry` linear and
injective. -/
class Entrywise (α : Type) (ι : outParam Type) [AddCommGroup α] [Module ℝ α] where
  entry : α → ι → ℝ
  /-- The point with the given coordinates; `Interval.linComb` builds bounds
  this way. -/
  ofEntry : (ι → ℝ) → α
  entry_ofEntry (f : ι → ℝ) (i : ι) : entry (ofEntry f) i = f i
  ofEntry_entry (a : α) : ofEntry (entry a) = a
  entry_add (a b : α) (i : ι) : entry (a + b) i = entry a i + entry b i
  entry_smul (c : ℝ) (a : α) (i : ι) : entry (c • a) i = c * entry a i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
