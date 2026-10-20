module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.ReduceByCostMono
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `PolyZonotope.reduceGirardCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.

## Inputs
* `h` – dependent generator count
* `h'` – larger dependent generator count
* `q` – independent generator count
* `q'` – larger independent generator count
* `n` – dimension
* `p` – number of factors

## Hypotheses
* `hh` – dependent count grows
* `hq` – independent count grows

## Conclusion
* the cost does not decrease
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.reduceGirardCost_mono {h h' q q' : ℕ} (n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.reduceGirardCost n p h q
      ≤ PolyZonotope.reduceGirardCost n p h' q' := by -- --- PROOF ---
  -- the joint width is what every term but the last is stated in
  have hs : h + q ≤ h' + q' := Nat.add_le_add hh hq
  have a := Cost.le_iff.mp (Cost.sort_mono hs)
  have b := Cost.le_iff.mp (PolyZonotope.reduceByCost_mono (p := p) (p' := p) n le_rfl hh hq hh hq)
  simp only [PolyZonotope.reduceGirardCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at a b ⊢
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
