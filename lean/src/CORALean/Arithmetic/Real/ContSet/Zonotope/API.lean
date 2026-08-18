import CORALean.Arithmetic.Real.ContSet.Zonotope.Helper.API

/-!
# Zonotopes: the operations

CORA's `zonotope` operations over the structure in `Structure`, each in the
shape CORA gives it. `reduce` is where the generator count is bounded — every
other operation grows it freely — and the rules it can run are `Helper.Reduce`.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix

variable {n m : ℕ}

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

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, and which it is goes no further — a caller
names an order and gets an over-approximation. -/
noncomputable def Zonotope.reduce (Z : Zonotope n) (o : ℕ) : Zonotope n :=
  Z.reduceGirard o

end CORALean.Arithmetic.Real
