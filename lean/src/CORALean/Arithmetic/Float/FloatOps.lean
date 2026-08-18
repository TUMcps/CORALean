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

class FloatOps (𝕋 : Type) where
  zero : 𝕋
  /-- Sign is a bit, so negation needs no direction. -/
  neg : 𝕋 → 𝕋
  addUp : 𝕋 → 𝕋 → 𝕋
  addDown : 𝕋 → 𝕋 → 𝕋
  mulUp : 𝕋 → 𝕋 → 𝕋
  mulDown : 𝕋 → 𝕋 → 𝕋
  /-- Exact, like `neg`: choosing between two floats invents no digits. -/
  minimum : 𝕋 → 𝕋 → 𝕋
  maximum : 𝕋 → 𝕋 → 𝕋
  /-- Exact in a binary format, where halving only moves the exponent. -/
  half : 𝕋 → 𝕋

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-! ## Subtraction

Derived, not assumed: negation is exact, so a directed difference is a directed
sum. -/

def subUp (a b : 𝕋) : 𝕋 := addUp a (neg b)
def subDown (a b : 𝕋) : 𝕋 := addDown a (neg b)

/-! ## Summation

A `Finset.sum` of rounded scalars is not available: `addUp` is not associative,
so the sum has to name its own bracketing. This one is right-nested, matching
`Fin.sum_univ_succ`, which is what makes the bounds provable by a single
induction. -/

def sumUp : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => addUp (f 0) (sumUp fun i => f i.succ)

def sumDown : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => addDown (f 0) (sumDown fun i => f i.succ)

/-- Exact. Not named `abs`, which would make `|·|` ambiguous wherever this
namespace is open. -/
def absolute (a : 𝕋) : 𝕋 := maximum a (neg a)

/-! ## Dot products

Round the products and the sum the same way. Every matrix operation in the layer
is built from these two, so a row of a matrix product and a coordinate of a
matrix-vector product are the same call. -/

def dotDown {n : ℕ} (a b : Vec 𝕋 n) : 𝕋 := sumDown fun k => mulDown (a k) (b k)
def dotUp {n : ℕ} (a b : Vec 𝕋 n) : 𝕋 := sumUp fun k => mulUp (a k) (b k)

/-- Row sums of absolute values, rounded up: the half-width of the hull of a
zonotope centred at zero with these generators. Every use of it is a bound. -/
def radius {n h : ℕ} (G : Mat 𝕋 n h) : Vec 𝕋 n := fun i => sumUp fun j => absolute (G i j)

/-! ## Rounded linear algebra

Each entry is a dot product. Both directions are kept: the stored value is the
lower one, and the gap to the upper is what a caller is charged. -/

def mulVecDown {m n : ℕ} (M : Mat 𝕋 m n) (v : Vec 𝕋 n) : Vec 𝕋 m := fun i => dotDown (M i) v
def mulVecUp {m n : ℕ} (M : Mat 𝕋 m n) (v : Vec 𝕋 n) : Vec 𝕋 m := fun i => dotUp (M i) v

def matMulDown {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => dotDown (M₁ i) (fun l => M₂ l j)
def matMulUp {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => dotUp (M₁ i) (fun l => M₂ l j)

/-- How far a stored entry can be from the exact product. -/
def matMulDiff {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => subUp (matMulUp M₁ M₂ i j) (matMulDown M₁ M₂ i j)


end CORALean.Arithmetic.Float
