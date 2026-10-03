import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.reexpPairs`

Each term of a model with each exponent `j ≤ eₖ` of one variable: the index set of that variable's
binomial expansion.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reexpPairs (k : Fin n) (T : Taylm 𝕋 n) : List ((𝕋 × (Fin n → ℕ)) × ℕ) :=
  T.terms.flatMap fun a => (List.range (a.2 k + 1)).map fun j => (a, j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
