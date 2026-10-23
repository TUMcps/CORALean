module

public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# `FiniteKleeneSignalBuilder/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =============================  `FiniteKleeneSignalBuilder.comb`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `comb(possiblyTrue,possiblyFalse)` of `kleeneSignal`: the value of the property at a time. -/
def FiniteKleeneSignalBuilder.comb (possiblyTrue possiblyFalse : Bool) : Kleene :=
  if possiblyTrue && !possiblyFalse then .tt else if possiblyFalse && !possiblyTrue then .ff
  else .uu


-- ===========================  `FiniteKleeneSignalBuilder.mapTime`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The builder with the time stamps of both signals mapped by `f`. -/
def FiniteKleeneSignalBuilder.mapTime {T T' : Type} (f : T → T') (b : FiniteKleeneSignalBuilder T) :
    FiniteKleeneSignalBuilder T' :=
  ⟨b.possiblyTrueSignal.mapTime f, b.possiblyFalseSignal.mapTime f⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
