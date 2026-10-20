module

public import CORALean.Specification.Kleene.Kleene

@[expose] public section

/-!
# Kleene disjunction

`or` of `kleene.m`: true if one is true, false if both are false, unknown otherwise.

## Inputs
* `lhs` – left operand
* `rhs` – right operand

## Output
* the Kleene disjunction
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `lhs | rhs`. -/
def Kleene.or (lhs rhs : Kleene) : Kleene :=
  -- 1. true if one is true
  let trueMask := lhs == .tt || rhs == .tt
  -- 2. false if both are false
  let falseMask := lhs == .ff && rhs == .ff
  -- 3. rest is unknown
  if trueMask then .tt else if falseMask then .ff else .uu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
