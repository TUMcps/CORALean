module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDriftCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.BilinCostMono
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadBilinCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapDepCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpMultiCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpGreedyCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.RelaxWidthMultiCostMono

@[expose] public section

/-!
# `ContSet/PolyZonotope/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ==============================  `PolyZonotope.eDriftCost_mono`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the factor count. -/
theorem PolyZonotope.eDriftCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.eDriftCost p ≤ PolyZonotope.eDriftCost p' := by
  simp only [PolyZonotope.eDriftCost, Cost.le_iff, Cost.ops_add]
  omega


-- ===============================  `PolyZonotope.mapCost_mono`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.mapCost_mono {h h' q q' : ℕ} (cf : Cost) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.mapCost cf h q ≤ PolyZonotope.mapCost cf h' q' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.add_le_add hh hq))


-- ==============================  `PolyZonotope.mtimesCost_mono`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.mtimesCost_mono {h h' q q' : ℕ} (m n : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.mtimesCost m n h q ≤ PolyZonotope.mtimesCost m n h' q' :=
  PolyZonotope.mapCost_mono _ hh hq


-- ============================  `PolyZonotope.quadMapDepCost_mono`  ============================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the factor and generator counts, so bounds on the operand's
sizes give a bound on the cost. -/
theorem PolyZonotope.quadMapDepCost_mono {p p' h h' : ℕ} (m n : ℕ) (hp : p ≤ p') (hh : h ≤ h') :
    PolyZonotope.quadMapDepCost m n p h ≤ PolyZonotope.quadMapDepCost m n p' h' :=
  PolyZonotope.bilinCost_mono _ hp hh hh


-- =============================  `PolyZonotope.reduceByCost_mono`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both absorbed counts, so a bound on how many generators a split
throws away gives a bound on the cost. -/
theorem PolyZonotope.reduceByCost_mono {r r' rI rI' : ℕ} (n : ℕ) (hr : r ≤ r') (hI : rI ≤ rI') :
    PolyZonotope.reduceByCost n r rI ≤ PolyZonotope.reduceByCost n r' rI' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add hr hI))


-- ==========================  `PolyZonotope.relaxExpGreedyCost_mono`  ========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the round count. -/
theorem PolyZonotope.relaxExpGreedyCost_mono {N N' : ℕ} (n p : ℕ) (csel : Cost) (h : N ≤ N') :
    PolyZonotope.relaxExpGreedyCost n p N csel ≤ PolyZonotope.relaxExpGreedyCost n p N' csel :=
  Nat.mul_le_mul_right _ h


-- ==========================  `PolyZonotope.relaxExpMultiCost_mono`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxExpMultiCost_mono {p p' : ℕ} (n : ℕ) (h : p ≤ p') :
    PolyZonotope.relaxExpMultiCost n p ≤ PolyZonotope.relaxExpMultiCost n p' :=
  Cost.add_le_add (le_refl _) (PolyZonotope.relaxWidthMultiCost_mono h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
