module

public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.comapCost`

Asserted, not proved: `Operations/Comap.lean` precomposes each of the `m`
inequality rows and `me` equality rows with `f` and leaves the right-hand sides
alone. What one precomposition costs depends on `f` and on how a row is held,
so it is a parameter, as `mapCost` takes what one application of `f` costs.

`cr` counts everything one precomposition does, the write of the new row included. At a
coordinate embedding such as `blockLeft` it is the writes of the dense-row reading
`HPolytope.halfScaledCost` states: the new row is the old one copied into a longer vector of
zeros, `d' + 1` writes at the new dimension `d'`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.comap` costs on `m` inequality and `me` equality rows when
precomposing one row costs at most `cr`. -/
def HPolytope.comapCost (m me : ℕ) (cr : Cost) : Cost := (m + me) • cr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
