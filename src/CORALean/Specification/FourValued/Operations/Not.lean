module

public import CORALean.Specification.FourValued.FourValued

@[expose] public section

/-!
# Four-valued negation

`not` of `fourValued.m`: swaps `True` and `False`, keeps `Unknown` and `Inconclusive`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `~op`. -/
def FourValued.not : FourValued → FourValued
  | .tt => .ff
  | .ff => .tt
  | .uu => .uu
  | .ii => .ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
