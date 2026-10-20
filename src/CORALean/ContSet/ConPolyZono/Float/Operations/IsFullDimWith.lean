module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ZeroMonomials
public import CORALean.ContSet.Zonotope.Float.Operations.BallCert
public import CORALean.ContSet.Zonotope.Float.Operations.BallB

@[expose] public section

/-!
# `ConPolyZono.isFullDimWith`, over a floating-point scalar

CORA's `@conPolyZono/isFullDim` asks for `rank([G GI]) = n`, which is necessary for a nonempty
interior and not sufficient. A sound test certifies the real property: if the factors `α = 0`
satisfy the constraints, the set contains a translate of the zonotope spanned by `GI`, so a right
inverse `H` of `GI` accepted by `Zonotope.ballCert` puts a box of positive radius inside the set.
Each row `A μ(0)` is enclosed by directed roundings and must be within the slack. `true` proves an
interior point; `false` refutes nothing.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `H` – matrix of independent generators

## Output
* whether the witness shows full dimension
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.isFullDimWith (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (H : Mat 𝕋 cPZ.qI n) : Bool :=
  Zonotope.ballCert (fun i j => cPZ.GI j i) H (Zonotope.ballB H one) one
    && (List.finRange cPZ.cons.m).all (fun i =>
      le (subUp (cPZ.cons.b i) (dotDown (cPZ.cons.A i) cPZ.zeroMonomials)) (absolute
          (cPZ.cons.b_error i))
        && le (subUp (dotUp (cPZ.cons.A i) cPZ.zeroMonomials) (cPZ.cons.b i)) (absolute
            (cPZ.cons.b_error i)))
    && (List.finRange n).all fun i => le (cPZ.I_error.inf i) (cPZ.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
