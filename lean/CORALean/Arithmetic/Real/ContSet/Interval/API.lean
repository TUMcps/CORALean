import CORALean.Global.API

/-!
# Intervals: representation and operations

CORA's `interval`, with the same `inf` and `sup` fields.

`sup i < inf i` gives the empty set, so no separate empty representation is
needed. `plus` is exact; `mtimes` is not, because a box cannot record that one
coordinate was used in two output rows. Its `min`/`max` bounds avoid a case
split on the sign of `M`.

Guarantees live in `Theorems`.
-/

namespace CORALean.Arithmetic.Real

variable {n m : ℕ}

structure Interval (n : ℕ) where
  inf : Vec ℝ n
  sup : Vec ℝ n

def Interval.construct (I : Interval n) : Set (Vec ℝ n) :=
  {x | ∀ i, I.inf i ≤ x i ∧ x i ≤ I.sup i}

instance : ContSet (Interval n) n := ⟨Interval.construct⟩

def Interval.plus (I₁ I₂ : Interval n) : Interval n where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

def Interval.mtimes (M : Mat ℝ m n) (I : Interval n) : Interval m where
  inf := fun i => ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
  sup := fun i => ∑ k, max (M i k * I.inf k) (M i k * I.sup k)

end CORALean.Arithmetic.Real
