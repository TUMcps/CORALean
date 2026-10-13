module

public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the centre and each of the
`h` generators through `f`, and touches nothing else.

What one `f` costs is a parameter, as in `PolyZonotope.mapCost` and for the
same reason: `f` is any linear map. `mtimesCost` is this at `Cost.matVec m n`,
the cost of `f := M *ᵥ ·`, though it is stated as its own `def` rather than
through this one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.map` costs at a map costing at most `cf` per application:
one per generator, and one for the centre. -/
def Zonotope.mapCost (cf : Cost) (h : ℕ) : Cost := (h + 1) • cf

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mapCost_mono {h h' : ℕ} (cf : Cost) (hh : h ≤ h') :
    Zonotope.mapCost cf h ≤ Zonotope.mapCost cf h' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
