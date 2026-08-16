import CORALean.Arithmetic.Real.ContSet.Interval.API

/-!
# Zonotopes: representation and operations

CORA's `zonotope`, with the same centre `c` and generator matrix `G`. The
generator count `h` sits in the type, so each signature reports what the
operation does to the representation.

`reduce` partitions the generator indices rather than choosing them: `part.left`
names the `q` generators kept, `part.right` the `r` absorbed into a diagonal
block holding their interval hull. Soundness holds for every `part`, so CORA's
twenty-odd selection rules are this one definition with a different partition
and none carries a proof obligation.

`interval` is the interval hull, CORA's `@zonotope/interval.m`.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix

variable {n m h k q r : ℕ}

structure Zonotope (n h : ℕ) where
  c : Vec ℝ n
  G : Mat ℝ n h

def Zonotope.construct (Z : Zonotope n h) : Set (Vec ℝ n) :=
  {x | ∃ β : Vec ℝ h, (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = Z.c i + ∑ j, Z.G i j * β j}

instance : ContSet (Zonotope n h) n := ⟨Zonotope.construct⟩

def Zonotope.plus (Z₁ : Zonotope n h) (Z₂ : Zonotope n k) : Zonotope n (h + k) where
  c := Z₁.c + Z₂.c
  G := fun i => Fin.append (Z₁.G i) (Z₂.G i)

def Zonotope.mtimes (M : Mat ℝ m n) (Z : Zonotope n h) : Zonotope m h where
  c := M *ᵥ Z.c
  G := M * Z.G

def Zonotope.interval (Z : Zonotope n h) : Interval n where
  inf := fun i => Z.c i - ∑ j, |Z.G i j|
  sup := fun i => Z.c i + ∑ j, |Z.G i j|

def Zonotope.reduce (Z : Zonotope n h) (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Zonotope n (q + n) where
  c := Z.c
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                           (Matrix.diagonal (fun i => ∑ l, |Z.G i (part.right l)|) i)

end CORALean.Arithmetic.Real
