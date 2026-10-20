module

public import CORALean.ContSet.Taylm.Real.Operations.CosyGo
public import CORALean.ContSet.Taylm.Real.Theorems.ExistsLeGlobalMin
public import CORALean.ContSet.Taylm.Real.Definitions.GoodBox
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# COSY-GO's upper end is above the minimum

[1, Sec. 4]: some point of `X` has a value at most the upper end, so `cosyGo` encloses the
minimum.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `X` – domain box
* `ε` – tolerance
* `ldbFuel` – fuel of the linear bounder
* `fuel` – step budget

## Hypotheses
* `h` – the model encloses the function
* `hX` – the box lies in the unit box
* `hX'` – the box ends are ordered

## Conclusion
* some point of the box has a value below the upper end

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exists_le_cosyGo {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {X : Fin n → Interval ℝ} (hX : Taylm.GoodBox X) (hX' : ∀ k, (X k).inf ≤ (X k).sup) (ε : ℝ)
    (ldbFuel fuel : ℕ) : -- --- CONCL ---
    ∃ p, Taylm.InBox X p ∧ f p ≤ (T.cosyGo X ε ldbFuel fuel).sup := by -- --- PROOF ---
  refine Taylm.exists_le_globalMin (fun p hp => ?_) hX' fuel
  have hpbox : p ∈ Taylm.box n := fun k => abs_le.2
    ⟨le_trans (hX k).1 (hp k).1, le_trans (hp k).2 (hX k).2.2.2⟩
  have := h p hpbox
  linarith [this.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
