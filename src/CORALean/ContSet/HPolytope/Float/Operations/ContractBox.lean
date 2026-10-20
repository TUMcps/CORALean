module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace
public import CORALean.ContSet.Interval.Float.Operations.Materialise

@[expose] public section

/-!
# `HPolytope.contractBox`

A box cut to a halfspace description, one row after another by `Interval.contractHalfspace`:
every inequality row `A_i x ≤ b_i`, then every equality row as its two halves, `Ae_i x ≤ beU_i`
and `-Ae_i x ≤ beLN_i`; the right-hand sides carry the error box. Each row reads the box the
previous one left; a single pass, not iterated to a fixpoint.

The result is a box holding the intersection of the box with the polytope, and in general more.
It is what a guard or an invariant is cut with where the set has no `Intersection` instance, the
float zonotope being one.

## Inputs
* `P` – H-polytope
* `I` – interval

## Output
* the box `I` cut by every row of `P` in turn, the equality rows as two halfspaces each
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `I` cut by every row of `P` in turn, the equality rows as two halfspaces each. -/
def HPolytope.contractBox (P : HPolytope 𝕋 (Vec 𝕋 n)) (I : Interval (Vec 𝕋 n)) :
    Interval (Vec 𝕋 n) :=
  let rows := (List.finRange P.m).map (fun i => (P.A i, P.bU i))      -- A_i x ≤ bU_i
    ++ (List.finRange P.me).map (fun i => (P.Ae i, P.beU i))          -- Ae_i x ≤ beU_i
    ++ (List.finRange P.me).map                                       -- -Ae_i x ≤ beLN_i
      (fun i => (-(P.Ae i), P.beLN i))
  rows.foldl (fun J r => (J.contractHalfspace r.1 r.2).materialise) I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
