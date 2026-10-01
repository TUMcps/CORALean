/-!
# `randverify`: which reach algorithm

`standard` is CORA's `linAlg = 'standard'`, `LinearSys.reachFloat`; `wrappingFree` is
`LinearSys.reachWrappingFreeFloat`. Named on the command line `standard` and `wrappingfree`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ========================================  MAIN TYPE  ========================================= --

inductive RandAlg where
  | standard
  | wrappingFree
deriving Repr, DecidableEq

/-- The command-line name. -/
def RandAlg.name : RandAlg → String
  | .standard => "standard"
  | .wrappingFree => "wrappingfree"

def RandAlg.ofString? : String → Option RandAlg
  | "standard" => some .standard
  | "wrappingfree" => some .wrappingFree
  | _ => none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
