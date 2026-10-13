import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace

/-!
# `HPolytope.contractBox`

A box cut to a halfspace description, one row after another by
`Interval.contractHalfspace`: every inequality row `A_i x ≤ b_i`, then every
equality row as its two halves, `Ae_i x ≤ sup be_i` and `-Ae_i x ≤ -inf be_i`.
Each row reads the box the previous one left, so a later row profits from an
earlier one's cut; a single pass, not iterated to a fixpoint.

The result is a box holding the box's intersection with the polytope, and in
general more: a polytope's corners are not a box's. It is what a guard or an
invariant is cut with where the set it cuts has no `Intersection` instance of
its own, the float zonotope being one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `I` cut by every row of `P` in turn, the equality rows as two halfspaces each. -/
def HPolytope.contractBox (P : HPolytope 𝕋 (Vec 𝕋 n)) (I : Interval (Vec 𝕋 n)) :
    Interval (Vec 𝕋 n) :=
  let rows := (List.finRange P.m).map (fun i => (P.A i, P.b i))      -- A_i x ≤ b_i
    ++ (List.finRange P.me).map (fun i => (P.Ae i, P.be.sup i))       -- Ae_i x ≤ sup be_i
    ++ (List.finRange P.me).map                                       -- -Ae_i x ≤ -inf be_i
      (fun i => (fun j => neg (P.Ae i j), neg (P.be.inf i)))
  rows.foldl (fun J r => (J.contractHalfspace r.1 r.2).materialise) I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
