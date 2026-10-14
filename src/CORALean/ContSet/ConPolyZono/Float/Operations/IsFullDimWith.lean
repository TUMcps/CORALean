module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ZeroMonomials
public import CORALean.ContSet.Zonotope.Float.Operations.BallCert
public import CORALean.ContSet.Zonotope.Float.Operations.BallB

@[expose] public section

/-!
# `ConPolyZono.isFullDimWith`, over a floating-point scalar

CORA's `@conPolyZono/isFullDim` asks for `rank([G GI]) = n` after an emptiness check, which is
necessary for a nonempty interior and not sufficient. A sound test certifies the real property
instead: if the factors `α = 0` satisfy the constraints, the set contains the translate of the
zonotope spanned by the independent generators `GI`, so a right inverse `H` of `GI` that the caller
proposes and the check of `Zonotope.ballCert` accepts puts a box of positive radius inside the set.
At `α = 0` a constraint generator survives exactly when its exponent column is zero
(`ConPolyZono.zeroMonomials`); each row `A μ(0)` is enclosed by directed roundings between the
bounds `b`. The error box must be nonempty. `true` proves an interior point; `false` refutes
nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.isFullDimWith (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (H : Mat 𝕋 cPZ.qI n) : Bool :=
  Zonotope.ballCert (fun i j => cPZ.GI j i) H (Zonotope.ballB H one) one
    && (List.finRange cPZ.m).all (fun i =>
      le (cPZ.b.inf i) (dotDown (cPZ.A i) cPZ.zeroMonomials)
        && le (dotUp (cPZ.A i) cPZ.zeroMonomials) (cPZ.b.sup i))
    && (List.finRange n).all fun i => le (cPZ.I_error.inf i) (cPZ.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
