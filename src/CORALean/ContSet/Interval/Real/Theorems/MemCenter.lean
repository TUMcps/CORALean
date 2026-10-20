module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty

@[expose] public section

/-!
# The center of a box lies in it

Nonemptiness is the whole hypothesis, and it is not decoration: `center` is the
midpoint of bounds that are allowed to cross, and on a box whose bounds have
crossed it lies outside both of them.

This is what lets a layer commit its nominal value to a box it was handed —
`Layer.linearWithError` does, an approximation error rarely being centered at
zero — without knowing anything about where the box came from.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – `I` is nonempty

## Conclusion
* the center lies in the interval
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mem_center (I : Interval α) (hI : I.IsNonempty (ι := ι)) : -- --- CONCL ---
    I.center ∈ I.construct := fun i => by
  have h : entry I.inf i ≤ entry I.sup i := hI i
  -- the midpoint read at one coordinate, which is where the two bounds compare
  have hc : entry I.center i = (2:ℝ)⁻¹ * (entry I.inf i + entry I.sup i) := by -- --- PROOF ---
    show entry ((2:ℝ)⁻¹ • (I.inf + I.sup)) i = _
    rw [entry_smul, entry_add]
  rw [hc]
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
