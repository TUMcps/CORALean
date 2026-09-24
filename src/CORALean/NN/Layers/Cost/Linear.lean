import CORALean.Global.Cost

/-!
# `Layer.linearCost`

Asserted, not proved: `Operations/Linear.lean` is `plus (mtimes W s) (embed b)` —
one `mtimes`, one `plus`, one embedded bias — and nothing else; the same three
calls `Transition.jumpCost` prices for a hybrid automaton's reset.

What `mtimes`, `plus` and the embedding cost are parameters, `S` being
abstract here: `mtimesCost` is this at `cMtimes := Cost.matVec m n`.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Layer.linear` costs, at what `mtimes`, `plus` and embedding the bias
cost: the three added. -/
def Layer.linearCost (cMtimes cPlus cEmbed : Cost) : Cost := cMtimes + cPlus + cEmbed

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
