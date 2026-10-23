module

public import CORALean.Global.Interfaces
public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Data.List.Chain

@[expose] public section

/-!
# The checked constructor

`sig = finiteSignal(time,value)`: CORA throws `wrongInputInConstructor` where a check fails, here
`none`.

## Inputs
* `T` – time type
* `V` – value type
* `time` – breakpoint times
* `value` – values per breakpoint

## Output
* the signal, or none if a constructor check fails
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = finiteSignal(time,value)`. -/
def FiniteSignal.mk? {T V : Type} [TimeOrder T] [Zero T] [DecidableEq V] (time : List T)
    (value : List V) : Option (FiniteSignal T V) :=
  -- the five checks of the constructor
  if time ≠ [] ∧ time.length = value.length ∧ time.Pairwise (· < ·) ∧ value.IsChain (· ≠ ·) ∧
      ∀ t ∈ time, 0 ≤ t then some ⟨time, value⟩ else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
