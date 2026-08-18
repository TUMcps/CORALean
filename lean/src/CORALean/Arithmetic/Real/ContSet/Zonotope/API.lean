import CORALean.Arithmetic.Real.ContSet.Interval.API

/-!
# Zonotopes: representation and operations

CORA's `zonotope`, with the same centre `c` and generator matrix `G`. The
generator count is a field, not a type index: operations grow it freely and
`reduce` is what bounds it, where the algorithm asks rather than everywhere.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix

variable {n m q r : ℕ}

structure Zonotope (n : ℕ) where
  h : ℕ
  c : Vec ℝ n
  G : Mat ℝ n h

def Zonotope.construct (Z : Zonotope n) : Set (Vec ℝ n) :=
  {x | ∃ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = Z.c i + ∑ j, Z.G i j * β j}

def Zonotope.plus (Z₁ Z₂ : Zonotope n) : Zonotope n where
  h := Z₁.h + Z₂.h
  c := Z₁.c + Z₂.c
  G := fun i => Fin.append (Z₁.G i) (Z₂.G i)

def Zonotope.mtimes (M : Mat ℝ m n) (Z : Zonotope n) : Zonotope m where
  h := Z.h
  c := M *ᵥ Z.c
  G := M * Z.G

/-- The interval hull, CORA's `@zonotope/interval.m`. -/
def Zonotope.interval (Z : Zonotope n) : Interval n where
  inf := fun i => Z.c i - ∑ j, |Z.G i j|
  sup := fun i => Z.c i + ∑ j, |Z.G i j|

/-- Partitions the generator indices rather than choosing them: `part.left` is
kept, `part.right` absorbed into a diagonal block. CORA's twenty-odd selection
rules are this definition with a different partition. -/
def Zonotope.reduce (Z : Zonotope n) (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Zonotope n where
  h := q + n
  c := Z.c
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                           (Matrix.diagonal (fun i => ∑ l, |Z.G i (part.right l)|) i)

/-- Reduce to order `o`, at most `o * n` generators: keep `q = (o - 1) * n`, and
the diagonal block `reduce` appends brings the count back to `o * n`. Already at
that order or below, nothing happens.

`Partition.split` keeps the first `q`. A named rule such as Girard's is this with
a sorting permutation composed in, and owes no proof of its own — `reduce_outer`
holds for every partition. -/
def Zonotope.reduceOrder (o : ℕ) (Z : Zonotope n) : Zonotope n :=
  if hlt : o * n < Z.h then
    have hle : (o - 1) * n ≤ Z.h :=
      le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
    Z.reduce ((Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
      (finCongr (Nat.add_sub_cancel' hle).symm))
  else Z

end CORALean.Arithmetic.Real
