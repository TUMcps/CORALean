module

public import CORALean.ContSet.Taylm.Float.Operations.BinomCoef
public import CORALean.ContSet.Taylm.Float.Operations.ReexpPairs

@[expose] public section

/-!
# `Taylm.reexpCoef`

The bracket of the new coefficient of a term at one exponent of the variable: the term's coefficient
times the bracketed binomial one, each corner by directed arithmetic.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reexpCoef (k : Fin n) (m r : 𝕋) (p : (𝕋 × (Fin n → ℕ)) × ℕ) : 𝕋 × 𝕋 :=
  let B := Taylm.binomCoef (p.1.2 k) p.2 m r
  (Interval.mulLo p.1.1 p.1.1 B.1 B.2, Interval.mulHi p.1.1 p.1.1 B.1 B.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
