module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the centre, each of the `h`
dependent generators and each of the `q` independent ones through `f`, and
touches nothing else — the exponent matrix is carried over whole.

What one `f` costs is not something this file can know, `f` being any linear
map, so it is a parameter: `cf` is a bound on one application. That is what
keeps the count an upper bound rather than a guess, and `mtimesCost` is this at
`cf := Cost.matVec m n`. A caller with no bound on `f` has no bound here
either, which is the honest reading of a cost at an arbitrary map.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.map` costs at a map costing at most `cf` per
application: one per generator of either block, and one for the centre. -/
def PolyZonotope.mapCost (cf : Cost) (h q : ℕ) : Cost := (h + q + 1) • cf

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.mapCost_mono {h h' q q' : ℕ} (cf : Cost) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.mapCost cf h q ≤ PolyZonotope.mapCost cf h' q' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.add_le_add hh hq))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
