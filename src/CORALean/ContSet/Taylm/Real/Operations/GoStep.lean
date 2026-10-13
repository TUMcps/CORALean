module

public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Operations.WidestCoord
public import CORALean.ContSet.Taylm.Real.Operations.BoxMid

@[expose] public section

/-!
# One box step of COSY-GO

[1, Sec. 4], for a lower bounder `lb` of a box and an upper estimate `ub` of a point: the first box
of the list is eliminated if its lower bound is above the cutoff; otherwise the cutoff is updated
with the estimate at its mid-point and the box is bisected along its widest direction, the halves
going to the end of the list. The list management is not specified by the source; this is a
queue.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.goStep (lb : (Fin n → ℝ × ℝ) → ℝ) (ub : Vec ℝ n → ℝ) :
    List (Fin n → ℝ × ℝ) × ℝ → List (Fin n → ℝ × ℝ) × ℝ
  | ([], cut) => ([], cut)
  | (B :: rest, cut) =>
    -- a box whose lower bound is above the cutoff is eliminated
    if cut < lb B then (rest, cut)
    -- otherwise the cutoff takes the mid-point estimate, and the box is bisected
    else match Taylm.widestCoord B with
      | none => (rest ++ [B], min cut (ub (Taylm.boxMid B)))
      | some β => (rest ++ [(Taylm.halveBox B β).1, (Taylm.halveBox B β).2],
          min cut (ub (Taylm.boxMid B)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
