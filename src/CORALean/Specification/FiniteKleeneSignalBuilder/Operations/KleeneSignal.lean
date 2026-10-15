module

public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Combine

@[expose] public section

/-!
# The three-valued signal

`sig = kleeneSignal(obj)`: the signals of the builder are combined pointwise by `comb`. The
property can only be true where only `possiblyTrueSignal` holds, only false where only
`possiblyFalseSignal` holds, and is unknown where both do, and, "for convenience", where neither
does (with masks a property can be neither). `finiteSignal.combine` throws if the constructor
rejects the result; here `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = kleeneSignal(obj)`. -/
noncomputable def FiniteKleeneSignalBuilder.kleeneSignal? (obj : FiniteKleeneSignalBuilder) :
    Option (FiniteSignal ℝ Kleene) :=
  FiniteSignal.combine? FiniteKleeneSignalBuilder.comb
    [obj.possiblyTrueSignal, obj.possiblyFalseSignal]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
