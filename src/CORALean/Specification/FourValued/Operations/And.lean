module

public import CORALean.Specification.FourValued.FourValued

@[expose] public section

/-!
# Four-valued conjunction

`and` of `fourValued.m`: true if both are true, false if one is false, unknown if one is unknown
and none is inconclusive, inconclusive otherwise.

The result is that of the Kleene conjunction on the under- and overapproximation of the operands,
joined to inconclusive where they differ, as in [1, Fig. 3].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `lhs & rhs`. -/
def FourValued.and (lhs rhs : FourValued) : FourValued :=
  -- 1. true if both are true
  let trueMask := lhs == .tt && rhs == .tt
  -- 2. false if one is false
  let falseMask := lhs == .ff || rhs == .ff
  -- 3. unknown if at least one is unknown, but none is inconclusive or false
  let unknownMask := !(trueMask || falseMask || lhs == .ii || rhs == .ii)
  -- 4. rest is inconclusive
  if trueMask then .tt else if falseMask then .ff else if unknownMask then .uu else .ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
