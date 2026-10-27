module

public import CORALean.Global.Cost

@[expose] public section

/-!
# `Layer.linearCost`

Asserted, not proved: `Operations/Linear.lean` is `plus (mtimes W s) (embed b)` —
one `mtimes`, one `plus`, one embedded bias — and nothing else; the same three
calls `Transition.step_jumpCost` prices for a hybrid automaton's reset.

What `mtimes`, `plus` and the embedding cost are parameters, `S` being
abstract here: `mtimesCost` is this at `cMtimes := Cost.matVec m n`.

## Inputs
* `cMtimes` – cost of the matrix product
* `cPlus` – cost of the sum
* `cEmbed` – cost of embedding the bias

## Output
* the three costs added
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Layer.linear` costs, at what `mtimes`, `plus` and embedding the bias
cost: the three added. -/
def Layer.linearCost (cMtimes cPlus cEmbed : Cost) : Cost := cMtimes + cPlus + cEmbed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
