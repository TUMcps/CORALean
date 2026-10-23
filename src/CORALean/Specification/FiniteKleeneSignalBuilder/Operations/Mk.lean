module

public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# The constructor

`obj = finiteKleeneSignalBuilder(dur)`: both signals are false on `[0,dur]`, as
`finiteSignal(dur,false)`. CORA throws in that constructor for a negative `dur` (`time` must be
nonnegative); here `none`.

Generic over the time type: at a float scalar nothing rounds, the only comparison being exact
(`TimeOrder`).

## Inputs
* `T` – time type
* `dur` – signal duration

## Output
* builder with both signals false, or none for a negative duration
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj = finiteKleeneSignalBuilder(dur)`. -/
def FiniteKleeneSignalBuilder.mk? {T : Type} [TimeOrder T] [Zero T] (dur : T) :
    Option (FiniteKleeneSignalBuilder T) :=
  (FiniteSignal.mk? [dur] [false]).bind fun possiblyTrueSignal =>
    (FiniteSignal.mk? [dur] [false]).map fun possiblyFalseSignal =>
      ⟨possiblyTrueSignal, possiblyFalseSignal⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
