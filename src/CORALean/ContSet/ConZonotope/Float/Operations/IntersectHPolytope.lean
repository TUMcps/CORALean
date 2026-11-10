module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `ConZonotope.intersectHPolytope`

CORA's `@polytope/and_` with a constrained zonotope (`aux_and_conZonotope`), over a floating-point
scalar. CORA adds, for every inequality `aᵀ x ≤ b`, the row `aᵀ G β + s r = m - aᵀ c` with a fresh
factor `s` in `[-1, 1]`, whose range `[m - r, m + r]` is `[min aᵀ x, b]` from a linear program. Here
the row stays an inequality on the coefficients, `aᵀ G β ≤ b - aᵀ c`, which a constrained zonotope
over floats admits: the same set, no program, no new factor. The polytope's slacks and error box
are folded into its rows (`HPolytope.absorbRounding`, an equality as its two halves); the right-hand
side is widened by what carrying the rows rounds off (`matMulDiff`) and by what the set's error box
can add to the row. The generators and the center are kept.

## Inputs
* `cZ` – float constrained zonotope
* `P` – halfspace polytope

## Output
* the points of `cZ` that lie in `P`, outer
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows of `P` carried onto the coefficients of `cZ`, widened by the carrying error and by the
error box, stacked under the set's own constraint. -/
def ConZonotope.intersectHPolytope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    ConZonotope 𝕋 (Vec 𝕋 n) :=
  let Q := P.absorbRounding                                  -- inequality rows, slacks folded in
  let Qe : HPolytope 𝕋 (Vec 𝕋 n) := { Q with I_error := cZ.I_error }   -- reads the set's error box
  let GT : Mat 𝕋 n cZ.h := fun i j => cZ.G j i
  { cZ with P := cZ.P.stackRows (HPolytope.ineqs (matMulDown Q.A GT)
      fun i => addUp (addUp (subUp (Q.b i) (dotDown (Q.A i) cZ.c))   -- b - aᵀ c
        (radius (matMulDiff Q.A GT) i)) (Qe.errUp (-(Q.A i)))) }     -- carrying error, error box

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
