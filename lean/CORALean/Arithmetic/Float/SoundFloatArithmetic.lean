import CORALean.Global.API

/-!
# Sound floating-point arithmetic

`SoundFloatArithmetic F` is what the floating-point layer assumes of its scalar:
a real interpretation `toReal`, and arithmetic that rounds in a stated direction
— `addUp` never returns less than the exact sum, `addDown` never more. Nothing
here fixes a format, so the proofs above it hold for binary64, for any other
precision, and for the exact arithmetic of `Arithmetic.Real`, which is the
instance at the bottom of this file.

Deliberately not IEEE 754. Rounding *to nearest* is not enough to bound anything
in a stated direction, and the axioms say nothing about how the bound is
achieved: an implementation may set the hardware rounding mode, or round to
nearest and step one ulp outward. Either discharges these obligations.

Since `toReal` is total and lands in ℝ, no instance can represent NaN or an
infinity. Overflow is thereby assumed away rather than modelled, and an
implementation owes a range argument for that. It is the one gap between these
axioms and a machine.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

class SoundFloatArithmetic (F : Type) where
  toReal : F → ℝ
  zero : F
  neg : F → F
  addUp : F → F → F
  addDown : F → F → F
  mulUp : F → F → F
  mulDown : F → F → F
  /-- Sign is a bit; negation loses nothing. -/
  toReal_neg (a : F) : toReal (neg a) = -toReal a
  toReal_zero : toReal zero = 0
  add_le_addUp (a b : F) : toReal a + toReal b ≤ toReal (addUp a b)
  addDown_le_add (a b : F) : toReal (addDown a b) ≤ toReal a + toReal b
  mul_le_mulUp (a b : F) : toReal a * toReal b ≤ toReal (mulUp a b)
  mulDown_le_mul (a b : F) : toReal (mulDown a b) ≤ toReal a * toReal b

export SoundFloatArithmetic (toReal zero neg addUp addDown mulUp mulDown
  toReal_neg toReal_zero add_le_addUp addDown_le_add mul_le_mulUp mulDown_le_mul)

variable {F : Type} [SoundFloatArithmetic F] {n : ℕ}

/-! ## Subtraction

Derived rather than assumed: negation is exact, so a directed difference is a
directed sum. -/

def subUp (a b : F) : F := addUp a (neg b)
def subDown (a b : F) : F := addDown a (neg b)

theorem sub_le_subUp (a b : F) : toReal a - toReal b ≤ toReal (subUp a b) := by
  rw [sub_eq_add_neg, ← toReal_neg b]
  exact add_le_addUp a (neg b)

theorem subDown_le_sub (a b : F) : toReal (subDown a b) ≤ toReal a - toReal b := by
  rw [sub_eq_add_neg, ← toReal_neg b]
  exact addDown_le_add a (neg b)

/-! ## Summation

A `Finset.sum` of rounded scalars is not available: `addUp` is not associative,
so the sum has to name its own bracketing. This one is right-nested, matching
`Fin.sum_univ_succ`, which is what makes the bounds provable by a single
induction. -/

def sumUp : {n : ℕ} → (Fin n → F) → F
  | 0, _ => zero
  | _ + 1, f => addUp (f 0) (sumUp fun i => f i.succ)

def sumDown : {n : ℕ} → (Fin n → F) → F
  | 0, _ => zero
  | _ + 1, f => addDown (f 0) (sumDown fun i => f i.succ)

theorem sum_le_sumUp (f : Fin n → F) : ∑ i, toReal (f i) ≤ toReal (sumUp f) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumUp, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumUp]
    exact le_trans (add_le_add (le_refl _) (ih _)) (add_le_addUp _ _)

theorem sumDown_le_sum (f : Fin n → F) : toReal (sumDown f) ≤ ∑ i, toReal (f i) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, sumDown, toReal_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, sumDown]
    exact le_trans (addDown_le_add _ _) (add_le_add (le_refl _) (ih _))

/-! ## Exact arithmetic as an instance

ℝ satisfies the axioms with both directions equal, so `Arithmetic.Real` is this
layer at infinite precision. It keeps the class demonstrably non-vacuous, and
any proof written against `SoundFloatArithmetic` can be read back on ℝ. -/

instance : SoundFloatArithmetic ℝ where
  toReal := id
  zero := 0
  neg := Neg.neg
  addUp := (· + ·)
  addDown := (· + ·)
  mulUp := (· * ·)
  mulDown := (· * ·)
  toReal_neg _ := rfl
  toReal_zero := rfl
  add_le_addUp _ _ := le_refl _
  addDown_le_add _ _ := le_refl _
  mul_le_mulUp _ _ := le_refl _
  mulDown_le_mul _ _ := le_refl _

end CORALean.Arithmetic.Float
