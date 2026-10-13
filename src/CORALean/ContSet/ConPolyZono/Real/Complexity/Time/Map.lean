module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConPolyZono.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the centre and each of the
`h` dependent and `q` independent generators through `f`, and touches nothing
else — the exponent matrix and the whole constraint system, `A`, `b`, `EC`,
carry over untouched.

What one `f` costs is a parameter, exactly as in `PolyZonotope.mapCost` and for
the same reason: `f` is any linear map.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.map` costs at a map costing at most `cf` per application:
one per generator of either block, and one for the centre. -/
def ConPolyZono.mapCost (cf : Cost) (h q : ℕ) : Cost := (h + q + 1) • cf

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.mapCost_mono {h h' q q' : ℕ} (cf : Cost) (hh : h ≤ h') (hq : q ≤ q') :
    ConPolyZono.mapCost cf h q ≤ ConPolyZono.mapCost cf h' q' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.add_le_add hh hq))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
