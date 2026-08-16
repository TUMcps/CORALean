import CORALean.Global.API

/-!
# Floating-point operations

The arithmetic a machine float offers, with no claim about what it computes:
two rounding directions per operation, and the exact operations that need none.
`SoundFloatArithmetic` is what says the directions are honest.

The split is what keeps the layer executable. A real interpretation cannot be
compiled, so any class carrying one is noncomputable, and so is every operation
reached through it. Definitions therefore assume only this class and run;
theorems assume both.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

class FloatOps (F : Type) where
  zero : F
  /-- Sign is a bit, so negation needs no direction. -/
  neg : F → F
  addUp : F → F → F
  addDown : F → F → F
  mulUp : F → F → F
  mulDown : F → F → F
  /-- Exact, like `neg`: choosing between two floats invents no digits. -/
  minimum : F → F → F
  maximum : F → F → F
  /-- Exact in a binary format, where halving only moves the exponent. An
  instance in some other radix could not provide this. -/
  half : F → F

open FloatOps

variable {F : Type} [FloatOps F]

/-! ## Subtraction

Derived rather than assumed: negation is exact, so a directed difference is a
directed sum. -/

def subUp (a b : F) : F := addUp a (neg b)
def subDown (a b : F) : F := addDown a (neg b)

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

/-! ## Dot products

Round the products and the sum the same way. Every matrix operation below is
built from these two, so a row of a matrix product and a coordinate of a
matrix-vector product are the same call. -/

def dotDown {n : ℕ} (a b : Vec F n) : F := sumDown fun k => mulDown (a k) (b k)
def dotUp {n : ℕ} (a b : Vec F n) : F := sumUp fun k => mulUp (a k) (b k)

end CORALean.Arithmetic.Float
