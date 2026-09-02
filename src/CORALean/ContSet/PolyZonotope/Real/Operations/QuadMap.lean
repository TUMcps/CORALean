import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent

/-!
# `PolyZonotope.quadMap`

CORA's `@polyZonotope/quadMap`, and the operation the representation exists for:
the image under `x ↦ (xᵀQ₁x, …, xᵀQₘx)` of a polynomial zonotope is a polynomial
zonotope, exactly. A zonotope has no such closure — the image of a zonotope
under a quadratic map is generally not a zonotope — and the reason this one does
is that the factors are shared: `mᵢ mⱼ` is again a monomial, in the exponent
column `Eᵢ + Eⱼ`.

Three definitions do the bookkeeping. `extG` folds the centre in as generator
zero and `extE` gives it the all-zero exponent column, so a point is one sum
rather than a centre plus a sum and the expansion is a plain double sum with no
case for the centre. The result is then indexed by pairs, through
`finProdFinEquiv`, since the structure carries a count and not an index type.

Independent generators are handled before the map rather than during it:
`quadMap` runs `quadMapDep` on `dependent`, whose independent block is empty by
construction. That is what keeps the operation total and exact at once —
`quadMapDep` alone is sound only where there is no independent block, and its
theorem says so.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n m : ℕ}

/-- The quadratic map itself: one matrix per output coordinate. -/
def PolyZonotope.quadEval (Q : Fin m → Mat ℝ n n) (x : Vec ℝ n) : Vec ℝ m :=
  fun k => x ⬝ᵥ (Q k *ᵥ x)

/-- The centre as generator zero. -/
def PolyZonotope.extG (S : PolyZonotope α) : Fin (S.h + 1) → α := Fin.cons S.c S.G

/-- The exponent matrix widened to match, the centre's column being zero — its
monomial is `1`, which is what the centre needs to be. -/
def PolyZonotope.extE (S : PolyZonotope α) : Fin S.p → Fin (S.h + 1) → ℕ :=
  fun k => Fin.cons 0 (S.E k)

def PolyZonotope.extM (S : PolyZonotope α) (a : Fin S.p → ℝ) : Fin (S.h + 1) → ℝ :=
  PolyZonotope.monomial (PolyZonotope.extE S) a

/-- Generator `(i, j)` of the image: `Gᵢᵀ Q Gⱼ`, one coordinate per matrix. -/
def PolyZonotope.quadMapG (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n)) :
    Fin ((S.h + 1) * (S.h + 1)) → Vec ℝ m :=
  fun l k => PolyZonotope.extG S (finProdFinEquiv.symm l).1
      ⬝ᵥ (Q k *ᵥ PolyZonotope.extG S (finProdFinEquiv.symm l).2)

/-- Its exponent column, the two columns added: the factors are shared, so the
product of two monomials is a monomial again. -/
def PolyZonotope.quadMapE (S : PolyZonotope α) :
    Fin S.p → Fin ((S.h + 1) * (S.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S k (finProdFinEquiv.symm l).2

/-- The map on a set whose coefficients are all dependent. Sound only there, so
nothing calls it directly. -/
def PolyZonotope.quadMapDep (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) where
  p := S.p
  h := (S.h + 1) * (S.h + 1)
  q := 0
  c := 0
  G := PolyZonotope.quadMapG Q S
  E := PolyZonotope.quadMapE S
  GI := Fin.elim0

def PolyZonotope.quadMap (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) := PolyZonotope.quadMapDep Q PZ.dependent

end CORALean.Real
