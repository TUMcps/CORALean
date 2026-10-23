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

Generic over the time type: at a float scalar nothing rounds, the only comparisons being exact
(`TimeOrder`).

## Inputs
* `T` – time type
* `obj` – signal builder

## Output
* the three-valued signal, or none if the combination fails
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = kleeneSignal(obj)`. -/
def FiniteKleeneSignalBuilder.kleeneSignal? {T : Type} [TimeOrder T] [Zero T]
    (obj : FiniteKleeneSignalBuilder T) : Option (FiniteSignal T Kleene) :=
  FiniteSignal.combine? FiniteKleeneSignalBuilder.comb
    [obj.possiblyTrueSignal, obj.possiblyFalseSignal]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
