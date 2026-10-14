module

public import CORALean.Specification.FourValued.FourValued

@[expose] public section

/-!
# Four-valued disjunction

`or` of `fourValued.m`: true if one is true, false if both are false, unknown if one is unknown
and none is inconclusive, inconclusive otherwise.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `lhs | rhs`. -/
def FourValued.or (lhs rhs : FourValued) : FourValued :=
  -- 1. true if one is true
  let trueMask := lhs == .tt || rhs == .tt
  -- 2. false if both are false
  let falseMask := lhs == .ff && rhs == .ff
  -- 3. unknown if at least one is unknown, but none is inconclusive or true
  let unknownMask := !(trueMask || falseMask || lhs == .ii || rhs == .ii)
  -- 4. rest is inconclusive
  if trueMask then .tt else if falseMask then .ff else if unknownMask then .uu else .ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
