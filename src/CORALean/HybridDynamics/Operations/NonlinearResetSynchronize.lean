import CORALean.HybridDynamics.Definitions.NonlinearReset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# `NonlinearReset.synchronize`

CORA's `nonlinearReset/synchronize`: the resets of several parallel components that act on the
same spaces, combined by summing their results; the coordinates `idStates` additionally keep the
pre-jump value (`f_sym(idStates) = x(idStates)`, then each `f_i` is added). Real, since the
sum of floats is not exact.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.synchronize (rs : Fin k → NonlinearReset n m n) (idStates : Finset (Fin n)) :
    NonlinearReset n m n where
  f := fun x u i => (if i ∈ idStates then x i else 0) + ∑ j, (rs j).f x u i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
