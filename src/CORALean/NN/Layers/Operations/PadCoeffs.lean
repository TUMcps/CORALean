import CORALean.Global.Float.FloatOps

/-!
# Stored coefficients read at a higher degree

`zero` for every coefficient the original does not have: exact, so a neuron below the layer's
maximum order pays nothing for the neurons above it. A `dite` on the index rather than a
`Fin.castLE`, which maps the smaller index type and so runs the wrong way.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Coefficients read at degree `M`, the ones the original does not have `zero`. -/
def padCoeffs (c : Fin (k + 1) → 𝕋) (M : ℕ) : Fin (M + 1) → 𝕋 :=
  fun j => if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
