module

public import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Operations.Transpose
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# `ProbZonotope.enclose`, over a floating-point scalar

CORA's `enclose(probZ, Ar, Rtrans)` [1, Sec. VI] in `𝕋`, one `let` per printed step of the real
`ProbZonotope.enclose`: `e^{Ar}` becomes the float interval enclosure
`MatExp.expIntervalEnclosure` of `[Ar, Ar]` at Taylor order `η`, `e^{Ar} - I` its interval sum
with `-I`, the product with the zonotope `Zonotope.mtimesIntervalMat`, CORA's zonotope `enclose`
the float `Zonotope.linComb`, and the covariance the interval product `[e^{Ar}] Σ [e^{Ar}]ᵀ`.
One step differs: the real operation multiplies the confidence set `zonotope(probZ, m)`, but the
float layer stores the covariance as an interval matrix with no square root, so `Zaux` is built
from the mean zonotope `Z` alone and `m` is no argument (`Theorems.EncloseMeanOuter`).

## Inputs
* `P` – probabilistic zonotope
* `Ar` – `n × n` matrix
* `η` – natural number
* `Rtrans` – vector of length `n`

## Output
* the probabilistic zonotope enclosing `P` and its image under `e^{Ar}`, in float arithmetic

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.enclose (P : ProbZonotope 𝕋 n) (Ar : Mat 𝕋 n n) (η : ℕ) (Rtrans : Vec 𝕋 n) :
    ProbZonotope 𝕋 n :=
  let expAr := MatExp.expIntervalEnclosure (Interval.point Ar) η           -- [e^{Ar}]
  let expArI := Interval.matPlus expAr                                     -- [e^{Ar}] - I
    (Interval.point (diagonalBlock fun _ => neg one))
  let Zaux := (Zonotope.mtimesIntervalMat expArI P.Z).plus                 -- ([e^{Ar}] - I) Z
    (Zonotope.point Rtrans)                                                --   + Rtrans
  let deltaZ := Zonotope.linComb (Zonotope.point fun _ => zero) Zaux       -- enclose(0, Zaux)
  { Z := P.Z.plus deltaZ                                                   -- Z + deltaZ
    cov := if ltStrict (sumUp fun i => Ar i i) zero                        -- trace(Ar) < 0
      then Interval.matMul (Interval.matMul expAr P.cov) expAr.transpose   -- [e^{Ar}] Σ [e^{Ar}]ᵀ
      else P.cov }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
