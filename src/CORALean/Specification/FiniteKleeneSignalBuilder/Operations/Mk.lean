module

public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# The constructor

`obj = finiteKleeneSignalBuilder(dur)`: both signals are false on `[0,dur]`, as
`finiteSignal(dur,false)`. CORA throws in that constructor for a negative `dur` (`time` must be
nonnegative); here `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj = finiteKleeneSignalBuilder(dur)`. -/
noncomputable def FiniteKleeneSignalBuilder.mk? (dur : ℝ) : Option FiniteKleeneSignalBuilder :=
  (FiniteSignal.mk? [dur] [false]).bind fun possiblyTrueSignal =>
    (FiniteSignal.mk? [dur] [false]).map fun possiblyFalseSignal =>
      ⟨possiblyTrueSignal, possiblyFalseSignal⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
