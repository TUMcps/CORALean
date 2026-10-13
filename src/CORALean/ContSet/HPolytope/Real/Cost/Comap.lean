import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.Global.Cost

/-!
# `HPolytope.comapCost`

Asserted, not proved: `Operations/Comap.lean` precomposes each of the `m`
inequality rows and `me` equality rows with `f` and leaves the right-hand sides
alone. What one precomposition costs depends on `f` and on how a row is held,
so it is a parameter, as `mapCost` takes what one application of `f` costs.

At a coordinate embedding such as `blockLeft` it is zero under the dense-row
reading `HPolytope.halfScaledCost` states: the new row is the old one copied
into a longer vector of zeros, which is data movement.
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

/-- Monotone in the row counts, so a bound on the operand's size gives a bound on
the cost. -/
theorem HPolytope.comapCost_mono {m m' me me' : ℕ} (cr : Cost) (hm : m ≤ m') (hme : me ≤ me') :
    HPolytope.comapCost m me cr ≤ HPolytope.comapCost m' me' cr :=
  Nat.mul_le_mul_right _ (Nat.add_le_add hm hme)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
