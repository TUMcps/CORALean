import CORALean.ContSet.ConZonotope.Real.Operations.Map
import CORALean.Global.Cost

/-!
# `ConZonotope.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the centre and each of the
`h` generators through `f` and carries the constraint polytope over as the
field it already is — `P := cZ.P`, untouched — so nothing the polytope holds
enters the count.

That is the one thing that makes a count possible here at all. `plus`, `and`
and `linComb` each *build* a polytope, and what building one costs depends on
how its rows are represented; `HPolytope` stores them as linear functionals and
fixes nothing, so those three are left uncounted. `Cost/API.lean` says so at
length.

What one `f` costs is a parameter, as in `PolyZonotope.mapCost` and for the same
reason: `f` is any linear map.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.map` costs at a map costing at most `cf` per application:
one per generator and one for the centre, and nothing for the constraints. -/
def ConZonotope.mapCost (cf : Cost) (h : ℕ) : Cost := (h + 1) • cf

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mapCost_mono {h h' : ℕ} (cf : Cost) (hh : h ≤ h') :
    ConZonotope.mapCost cf h ≤ ConZonotope.mapCost cf h' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
