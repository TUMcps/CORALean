import CORALean.ContSet.Taylm.Float.Taylm

/-!
# `Taylm.bernsteinIdx`

Every multi-index `Fin n → Fin (N + 1)` of the Bernstein coefficients, as a list the float
minimum and maximum run over.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bernsteinIdx : (n N : ℕ) → List (Fin n → Fin (N + 1))
  | 0, _ => [fun i => i.elim0]
  | n + 1, N => (List.finRange (N + 1)).flatMap fun j =>
    (Taylm.bernsteinIdx n N).map (Fin.cons (α := fun _ => Fin (N + 1)) j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
