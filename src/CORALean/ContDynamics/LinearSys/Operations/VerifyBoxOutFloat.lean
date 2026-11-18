module

public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `LinearSys.verifyBoxOutFloat`, generators moved into the box

The generators flagged `false` leave the list and their magnitudes join the box: `b + Σ |g|` over
them, summed in their order and added to `b` last, every addition rounded up. The ones flagged
`true` stay, in their order. A generator `β g`, `|β| ≤ 1`, lies in the box `|g|`, so the result
encloses what it was given (CORA's reduction of the input's solution in `priv_reach_adaptive`).

## Inputs
* `L` – float generators, each flagged to stay
* `b` – float radius of the box

## Output
* the generators that stay and the enlarged box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators flagged `true`, and `b` plus the magnitudes of the others. -/
def LinearSys.verifyBoxOutFloat (L : List (Vec 𝕋 n × Bool)) (b : Vec 𝕋 n) :
    List (Vec 𝕋 n) × Vec 𝕋 n :=
  let out := fun i => (L.filter fun g => !g.2).foldl (fun acc g =>      -- Σ |g| over those leaving
    addUp acc (absolute (g.1 i))) zero
  ((L.filter fun g => g.2).map Prod.fst,
    (Interval.point fun i => addUp (b i) (out i)).materialise.sup)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
