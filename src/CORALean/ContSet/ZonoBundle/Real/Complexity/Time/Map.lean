module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Map

@[expose] public section

/-!
# `ZonoBundle.mapCost`

Asserted, not proved: `Operations/Map.lean` runs `Zonotope.map` once per member
and does nothing of its own, so the count is `k` copies of the zonotope one.

`h` bounds *every* member's generator count, as in `ZonoBundle.mtimesCost`,
since the structure carries a family with no common width.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.map` costs at a map costing at most `cf` per application,
on a bundle of `k` members, none of them over `h` generators. -/
def ZonoBundle.mapCost (cf : Cost) (k h : ℕ) : Cost := k • Zonotope.mapCost cf h

/-- Monotone in the member count and in the generator bound, so bounds on the
operand's sizes give a bound on the cost. -/
theorem ZonoBundle.mapCost_mono {k k' h h' : ℕ} (cf : Cost) (hk : k ≤ k') (hh : h ≤ h') :
    ZonoBundle.mapCost cf k h ≤ ZonoBundle.mapCost cf k' h' :=
  Nat.mul_le_mul hk (Cost.le_iff.mp (Zonotope.mapCost_mono cf hh))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
