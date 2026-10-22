module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.BilinCostMono
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapDepCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpGreedyCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti

@[expose] public section

/-!
# `ContSet/PolyZonotope/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ============================  `PolyZonotope.quadMapDepCost_mono`  ============================ --
-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the factor and generator counts, so bounds on the operand's
sizes give a bound on the cost. -/
theorem PolyZonotope.quadMapDepCost_mono {p p' h h' : ℕ} (m n : ℕ) (hp : p ≤ p') (hh : h ≤ h') :
    PolyZonotope.quadMapDepCost m n p h ≤ PolyZonotope.quadMapDepCost m n p' h' :=
  PolyZonotope.bilinCost_mono _ le_rfl hp hh hh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
