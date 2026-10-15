module

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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
