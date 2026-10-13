import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Dependent
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# `PolyZonotope.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` is `quadMapDep` after
`dependent`, and `dependentCost` is zero, so the whole count is `quadMapDepCost`
at the sizes `dependent` leaves — `p + q` factors and `h + q` dependent
generators, both proved in `Complexity/Space/Dependent.lean`.

That the independent generators enter the *square* is the operation's own
doing and the reason a caller reduces before mapping rather than after: `q`
free coefficients cost `q` dependent generators here, and `(h+q)²` pairs after
that.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.quadMap` costs at `m` matrices of size `n × n`: the
dependent map at the counts `dependent` leaves, the conversion itself free. -/
def PolyZonotope.quadMapCost (m n p h q : ℕ) : Cost :=
  PolyZonotope.dependentCost + PolyZonotope.quadMapDepCost m n (p + q) (h + q)

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.quadMapCost_mono {h h' q q' : ℕ} (m n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.quadMapCost m n p h q ≤ PolyZonotope.quadMapCost m n p h' q' := by
  -- `dependent` is free, so the comparison is the dependent map's at the counts it leaves
  have h := PolyZonotope.quadMapDepCost_mono m n (Nat.add_le_add_left hq p) (Nat.add_le_add hh hq)
  simpa [PolyZonotope.quadMapCost, PolyZonotope.dependentCost] using h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
