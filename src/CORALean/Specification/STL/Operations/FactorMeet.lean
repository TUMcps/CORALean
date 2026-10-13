import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic

/-!
# The intersection of two unions of factor polytopes

Line 12 of [1, Alg. 2], `V ← (V(1) ∩ W(1), ..., V(|V|) ∩ W(|W|))`, as the intersection of the
unions `⋃V` and `⋃W` it stands for: every `V(a) ∩ W(b)`, `|V| · |W|` polytopes, as
`⋃V ∩ ⋃W = ⋃_{a,b} V(a) ∩ W(b)` needs. Read index by index, which the printed tuple suggests, only
`min(|V|, |W|)` of them are formed and unsafe factors are lost; `STL.factorMeet_zip_counterexample`.
CORA's `aux_orConstraints` forms all pairs.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2, l. 12]: `V(a) ∩ W(b)` for all `a`, `b`. -/
def STL.factorMeet (V W : List (Set X)) : List (Set X) :=
  V.flatMap fun v => W.map fun w => v ∩ w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
