module

public import CORALean.ContSet.Taylm.Float.Operations.BernsteinCoeffBounds
public import CORALean.ContSet.Taylm.Float.Operations.BernsteinIdx
public import CORALean.ContSet.Taylm.Float.Operations.ListMin
public import CORALean.ContSet.Taylm.Float.Operations.ListMax

@[expose] public section

/-!
# `Taylm.optBernstein`, over a floating-point scalar

CORA's `optBernstein`: the least and greatest Bernstein coefficient of the polynomial part over
`[-1, 1]ⁿ`, at the degree `max(max(E))`, plus the remainder. Each coefficient is a pair of floats
(`bernsteinCoeffBounds`, binomial ratios rounded outward); the bound takes the least lower end and
the greatest upper end over all multi-indices, and adds the remainder, the ends rounded outward.
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

def Taylm.optBernstein (T : Taylm 𝕋 n) : 𝕋 × 𝕋 :=
  let N := (T.terms.map fun a => Finset.univ.sup a.2).foldr max 0            -- n = max(max(E))
  let I := Taylm.bernsteinIdx n N                                           -- all multi-indices
  (addDown (Taylm.listMin (fun β => (Taylm.bernsteinCoeffBounds T.terms N β).1) I) T.remInf,
    addUp (Taylm.listMax (fun β => (Taylm.bernsteinCoeffBounds T.terms N β).2) I) T.remSup)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
