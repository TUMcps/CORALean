/-!
# `randverify`: which reach algorithm

`standard` is CORA's `linAlg = 'standard'`, `LinearSys.reachFloat`; `wrappingFree` is
`LinearSys.reachWrappingFreeFloat`. Named on the command line `standard` and `wrappingfree`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ========================================  MAIN TYPE  ========================================= --

/-- The reach algorithm `randverify` runs: CORA's standard one, or the wrapping-free one. -/
inductive RandAlg where
  | standard
  | wrappingFree
deriving Repr, DecidableEq

/-- The command-line name. -/
def RandAlg.name : RandAlg → String
  | .standard => "standard"
  | .wrappingFree => "wrappingfree"

/-- The algorithm named on the command line, `standard` or `wrappingfree`. -/
def RandAlg.ofString? : String → Option RandAlg
  | "standard" => some .standard
  | "wrappingfree" => some .wrappingFree
  | _ => none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
