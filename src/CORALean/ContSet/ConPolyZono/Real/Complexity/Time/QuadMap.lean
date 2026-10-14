module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.QuadMapDep

@[expose] public section

/-!
# `ConPolyZono.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` is `quadMapDep` after
`dependent`, and `quadMapDep`'s own generators and exponent matrix are exactly
`PolyZonotope.quadMapDep`'s, run on the enclosing polynomial zonotope — the
constraint system passes through untouched. So the whole count is
`PolyZonotope.quadMapDepCost` at the sizes `dependent` leaves: `p + qI` factors
and `h + qI` dependent generators, both proved in `Complexity/Space/QuadMap.lean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.quadMap` costs at `m` matrices of size `n × n`: the
polynomial-zonotope quadratic map at the counts `dependent` leaves, the
conversion itself free. -/
def ConPolyZono.quadMapCost (m n p h qI : ℕ) : Cost :=
  ConPolyZono.dependentCost + PolyZonotope.quadMapDepCost m n (p + qI) (h + qI)

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.quadMapCost_mono {h h' qI q' : ℕ} (m n p : ℕ) (hh : h ≤ h') (hq : qI ≤ q') :
    ConPolyZono.quadMapCost m n p h qI ≤ ConPolyZono.quadMapCost m n p h' q' := by
  -- `dependent` is free, so the comparison is the quadratic map's at the counts it leaves
  have h := PolyZonotope.quadMapDepCost_mono m n (Nat.add_le_add_left hq p) (Nat.add_le_add hh hq)
  simpa [ConPolyZono.quadMapCost, ConPolyZono.dependentCost] using h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
