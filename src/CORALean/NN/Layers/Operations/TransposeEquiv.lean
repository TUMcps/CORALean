module

public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Reading a two-dimensional array the other way round

The reshape a layout change is: a `p × q` array read as `q × p`. Flattening is not a layer
at all — `Vec ℝ (p * q)` is what a layer sees either way — so this relabelling is the only
content a reshape has. It carries no scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Reading a `p × q` array the other way round. -/
def Fin.transposeEquiv (p q : ℕ) : Fin (q * p) ≃ Fin (p * q) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin q) (Fin p)).trans finProdFinEquiv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
