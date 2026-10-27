module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_IntervalMatrix
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `VPolytope.matMul`, over a floating-point scalar

CORA's `mtimes` of two matrix polytopes: the products of every vertex of the first with every
vertex of the second, in the order of `Real.VPolytope.bilin`. The nominal products are rounded
down and their gap to the upward rounding goes into the error box. The error terms of `(a + e)(b +
f) = ab + af + e (b + f)` are interval products: `a` in the box of the first polytope's nominal
vertices, `b + f` in the box of the second polytope.

## Inputs
* `P` – first matrix polytope
* `Q` – second matrix polytope

## Output
* matrix polytope of the products with its error terms
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The box from `0` to the widest rounding gap of each entry over the vertices. -/
def VPolytope.aux_matColumnGap {k : ℕ} (lo hi : Fin k → Mat 𝕋 p r) : Interval (Mat 𝕋 p r) :=
  ⟨fun _ _ => zero, fun i j => maximumOver fun l => subUp (hi l i j) (lo l i j)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pairwise vertex products, rounded down, with the gap and the two error terms in the box. -/
def VPolytope.matMul (P : VPolytope (Mat 𝕋 p q)) (Q : VPolytope (Mat 𝕋 q r)) :
    VPolytope (Mat 𝕋 p r) where
  k := P.k * Q.k
  V := fun l => matMulDown (P.V (finProdFinEquiv.symm l).1) (Q.V (finProdFinEquiv.symm l).2)
  I_error := Interval.matPlus
    (VPolytope.aux_matColumnGap
      (fun l => matMulDown (P.V (finProdFinEquiv.symm l).1) (Q.V (finProdFinEquiv.symm l).2))
      (fun l => matMulUp (P.V (finProdFinEquiv.symm l).1) (Q.V (finProdFinEquiv.symm l).2)))
    (Interval.matPlus
      (Interval.matMul ({ P with I_error := Interval.point fun _ _ => zero } :
        VPolytope (Mat 𝕋 p q)).intervalMatrix Q.I_error)
      (Interval.matMul P.I_error Q.intervalMatrix))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
