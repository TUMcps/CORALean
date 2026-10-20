module

public import CORALean.HybridDynamics.Definitions.NonlinearReset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `NonlinearReset.synchronize`

CORA's `nonlinearReset/synchronize`: the resets of several parallel components that act on the
same spaces, combined by summing their results; the coordinates `idStates` additionally keep the
pre-jump value (`f_sym(idStates) = x(idStates)`, then each `f_i` is added). Real, since the
sum of floats is not exact.

## Inputs
* `rs` – component resets
* `idStates` – states kept by identity

## Output
* reset summing the components
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.synchronize (rs : Fin k → NonlinearReset n m n) (idStates : Finset (Fin n)) :
    NonlinearReset n m n where
  f := fun x u i => (if i ∈ idStates then x i else 0) + ∑ j, (rs j).f x u i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
