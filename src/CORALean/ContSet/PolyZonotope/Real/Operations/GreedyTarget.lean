import Mathlib.Data.List.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Defs.Unbundled

/-!
# `PolyZonotope.greedyTarget`

`greedy(G)` of `[1, Alg. 2]`, line 2, for a weighted directed graph on `Fin h`: node `i` keeps
only its outgoing edge of smallest weight, `none` where it has no outgoing edge. The paper does
not break ties between equal weights; the least target index is taken.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The target of node `i`'s outgoing edge of smallest weight `w`, the least index among ties. -/
def PolyZonotope.greedyTarget {h : ℕ} (G : Fin h → Fin h → Prop) [DecidableRel G]
    (w : Fin h → Fin h → ℕ) (i : Fin h) : Option (Fin h) :=
  (List.finRange h).foldl
    (fun best j =>
      if G i j then
        match best with
        | none => some j
        | some b => if w i j < w i b then some j else some b
      else best)
    none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
