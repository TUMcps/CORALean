module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `OnlineReachSetAnalyzer/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- ===========================  `OnlineReachSetAnalyzer.Formula.ap?`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The atomic proposition of an atom, the extra argument of an `AP` node. -/
def OnlineReachSetAnalyzer.Formula.ap? : OnlineReachSetAnalyzer.Formula A → Option A
  | .ap _ a => some a
  | _ => none


-- ========================  `OnlineReachSetAnalyzer.Formula.interval?`  ======================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The time interval of an `until`, the extra argument of an `until` node. -/
def OnlineReachSetAnalyzer.Formula.interval? : OnlineReachSetAnalyzer.Formula A →
    Option STLInterval
  | .until I _ _ => some I
  | _ => none


-- ===========================  `OnlineReachSetAnalyzer.updateNode`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj.nodes(i).f()`: applies `f` to the node with index `i`; MATLAB's index error, and a failing
`f`, are `none`. -/
def OnlineReachSetAnalyzer.updateNode {B : Type} (nodes : List B) (i : ℕ) (f : B → Option B) :
    Option (List B) :=
  if i = 0 then none else nodes[i - 1]?.bind fun n => (f n).map fun n' => nodes.set (i - 1) n'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
