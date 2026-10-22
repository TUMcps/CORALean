module

public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Tensor

@[expose] public section

/-!
# Operations derived from the floating-point operations

What `FloatOps` (in `Interfaces.lean`) gives without further assumption: directed subtraction, sums
and repeated addition, the extrema folds, the strict margin, dot products and matrix products. The
folds recurse so that proofs about them are one induction, and run as loops because `@[csimp]` swaps
in a `Fin.foldr` version, which the compiler accepts only with the proof of equality beside it, so
the trusted base is untouched.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ======================================  MAIN INSTANCE  ======================================= --

/-- A float negates itself, exactly. Low priority, so that a scalar with a `Neg` of its own
(`ℝ`) keeps it; the vectors and matrices of floats negate entrywise through `Pi.instNeg`. -/
instance (priority := low) : Neg 𝕋 := ⟨neg⟩

/-! ## Subtraction

Derived, not assumed: negation is exact, so a directed difference is a directed
sum. -/

/-- The difference `a - b` rounded up. -/
def subUp (a b : 𝕋) : 𝕋 := addUp a (neg b)
/-- The difference `a - b` rounded down. -/
def subDown (a b : 𝕋) : 𝕋 := addDown a (neg b)

/-! ## Summation

`addUp` is not associative, so a sum has to name its own bracketing rather than
go through `Finset.sum`. Right-nested, matching `Fin.sum_univ_succ`, so the
bounds are one induction. -/

/-- The sum of `f 0, …, f (n-1)`, nested to the right, every addition rounded up. -/
def sumUp : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => addUp (f 0) (sumUp fun i => f i.succ)

/-- The sum of `f 0, …, f (n-1)`, nested to the right, every addition rounded down. -/
def sumDown : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | _ + 1, f => addDown (f 0) (sumDown fun i => f i.succ)

/-- `Fin.foldr` nests to the right, which is what makes this the same sum and
not merely an equal one: the bracketing is the definition's. -/
def sumUpImpl {n : ℕ} (f : Fin n → 𝕋) : 𝕋 := Fin.foldr n (fun i acc => addUp (f i) acc) zero

/-- `sumDown` as a right fold, which compiles to a loop. -/
def sumDownImpl {n : ℕ} (f : Fin n → 𝕋) : 𝕋 := Fin.foldr n (fun i acc => addDown (f i) acc) zero

/-- The recursive `sumUp` is replaced by the fold `sumUpImpl` in compiled code. -/
@[csimp] theorem sumUp_eq_impl : -- --- CONCL ---
    @sumUp = @sumUpImpl := by -- --- PROOF ---
  funext 𝕋 _ n
  induction n with
  | zero => funext f; rw [sumUpImpl, Fin.foldr_zero]; rfl
  | succ n ih =>
    funext f
    -- The recursion peels `f 0`; `Fin.foldr_succ` peels the same entry.
    rw [sumUpImpl, Fin.foldr_succ, ← sumUpImpl, ← congrFun ih fun i => f i.succ]
    rfl

/-- The recursive `sumDown` is replaced by the fold `sumDownImpl` in compiled code. -/
@[csimp] theorem sumDown_eq_impl : -- --- CONCL ---
    @sumDown = @sumDownImpl := by -- --- PROOF ---
  funext 𝕋 _ n
  induction n with
  | zero => funext f; rw [sumDownImpl, Fin.foldr_zero]; rfl
  | succ n ih =>
    funext f
    rw [sumDownImpl, Fin.foldr_succ, ← sumDownImpl, ← congrFun ih fun i => f i.succ]
    rfl

/-! ## Repeated addition

A count of copies, one fold per direction. The count comes from an exponent
matrix, which is over ℕ in both layers, so only the additions round. -/

/-- `k` times `a` by repeated addition rounded down. -/
def nsmulDown : ℕ → 𝕋 → 𝕋
  | 0, _ => zero
  | k + 1, a => addDown a (nsmulDown k a)

/-- `k` times `a` by repeated addition rounded up. -/
def nsmulUp : ℕ → 𝕋 → 𝕋
  | 0, _ => zero
  | k + 1, a => addUp a (nsmulUp k a)

/-- The largest of `n` values, seeded at the last of them, so a hull of values that all lie on one
side of the origin does not reach the origin. `zero` only for no values at all. Exact, as `maximum`
is, so it needs no direction. -/
def maximumOver : {n : ℕ} → (Fin n → 𝕋) → 𝕋
  | 0, _ => zero
  | 1, f => f 0
  | _ + 2, f => maximum (f 0) (maximumOver fun i => f i.succ)

/-- Right-nested like `maximumOver`. `maximum` is associative where `addUp` is
not, so here the bracketing is a matter of cost alone. -/
def maximumOverImpl {n : ℕ} (f : Fin n → 𝕋) : 𝕋 :=
  match n, f with
  | 0, _ => zero
  | k + 1, f => Fin.foldr k (fun i acc => maximum (f i.castSucc) acc) (f (Fin.last k))

/-- The recursive `maximumOver` is replaced by the fold `maximumOverImpl` in compiled code. -/
@[csimp] theorem maximumOver_eq_impl : -- --- CONCL ---
    @maximumOver = @maximumOverImpl := by -- --- PROOF ---
  funext 𝕋 _ n
  induction n with
  | zero => funext f; rfl
  | succ k ih =>
    funext f
    cases k with
    | zero => rfl
    | succ k =>
      rw [maximumOver, congrFun ih fun i => f i.succ]
      simp only [maximumOverImpl, Fin.foldr_succ]
      rfl

/-- The smallest of `n` values, `zero` only for none. `neg` and `maximum` are both
exact, so the reflection costs nothing and no second fold is needed. -/
def minimumOver {n : ℕ} (f : Fin n → 𝕋) : 𝕋 := neg (maximumOver (-f))

/-- Exact. Not named `abs`, which would make `|·|` ambiguous wherever this
namespace is open. -/
def absolute (a : 𝕋) : 𝕋 := maximum a (neg a)

/-! ## Strict comparison

`le` certifies `≤` only, which cannot keep two closed sets apart. `ltStrict` asks `le`
of `a` raised by a positive margin, rounded up, so a `true` still certifies `<`. -/

/-- `2⁻⁶⁴`, exactly: `one` halved, and `half` rounds nothing. -/
def strictMargin : 𝕋 := half^[64] one

/-- A strict comparison: `a` plus the strict margin, rounded up, is at most `b`. -/
def ltStrict (a b : 𝕋) : Bool := le (addUp a strictMargin) b

/-! ## Dot products

Products and sum rounded the same way. Every matrix operation in the layer is
built from these two. -/

/-- The dot product with every product and sum rounded down. -/
def dotDown {n : ℕ} (a b : Vec 𝕋 n) : 𝕋 := sumDown fun k => mulDown (a k) (b k)
/-- The dot product with every product and sum rounded up. -/
def dotUp {n : ℕ} (a b : Vec 𝕋 n) : 𝕋 := sumUp fun k => mulUp (a k) (b k)

/-- Row sums of absolute values, rounded up: the half-width of the hull of a
zonotope centered at zero with these generators. -/
def radius {n h : ℕ} (G : Mat 𝕋 n h) : Vec 𝕋 n := fun i => sumUp fun j => absolute (G i j)

/-- One generator per coordinate. Not `Matrix.diagonal`, which needs `Zero 𝕋`,
and giving `𝕋` one would collide with ℝ's on the `SoundFloatArithmetic ℝ`
instance. -/
def diagonalBlock {n : ℕ} (v : Vec 𝕋 n) : Mat 𝕋 n n := fun i l => if i = l then v i else zero

/-! ## Rounded linear algebra

Each entry is a dot product. Both directions are kept: the stored value is the
lower one, the gap to the upper what a caller is charged. -/

/-- The matrix-vector product with every entry rounded down. -/
def mulVecDown {m n : ℕ} (M : Mat 𝕋 m n) (v : Vec 𝕋 n) : Vec 𝕋 m := fun i => dotDown (M i) v
/-- The matrix-vector product with every entry rounded up. -/
def mulVecUp {m n : ℕ} (M : Mat 𝕋 m n) (v : Vec 𝕋 n) : Vec 𝕋 m := fun i => dotUp (M i) v

/-- The matrix product with every entry rounded down. -/
def matMulDown {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => dotDown (M₁ i) (fun l => M₂ l j)
/-- The matrix product with every entry rounded up. -/
def matMulUp {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => dotUp (M₁ i) (fun l => M₂ l j)

/-- How far a stored entry can be from the exact product. -/
def matMulDiff {m n k : ℕ} (M₁ : Mat 𝕋 m n) (M₂ : Mat 𝕋 n k) : Mat 𝕋 m k :=
  fun i j => subUp (matMulUp M₁ M₂ i j) (matMulDown M₁ M₂ i j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
