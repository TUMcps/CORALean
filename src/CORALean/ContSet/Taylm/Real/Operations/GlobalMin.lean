module

public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Operations.ListMin
public import CORALean.ContSet.Taylm.Real.Operations.WidestCoord

@[expose] public section

/-!
# A verified enclosure of the minimum

[1, Sec. 4]: start from `X` with the cutoff at its mid-point estimate, run the box steps, and
return the least of the cutoff and the live boxes' lower bounds, and the cutoff: the minimum of the
function over `X` lies between them.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

noncomputable def Taylm.aux_goStep (lb : (Fin n → Interval ℝ) → ℝ) (ub : Vec ℝ n → ℝ) :
    List (Fin n → Interval ℝ) × ℝ → List (Fin n → Interval ℝ) × ℝ
  | ([], cut) => ([], cut)
  | (B :: rest, cut) =>
    -- a box whose lower bound is above the cutoff is eliminated
    if cut < lb B then (rest, cut)
    -- otherwise the cutoff takes the mid-point estimate, and the box is bisected
    else match Taylm.widestCoord B with
      | none => (rest ++ [B], min cut (ub (Taylm.boxMid B)))
      | some β => (rest ++ [(Taylm.halveBox B β).1, (Taylm.halveBox B β).2],
          min cut (ub (Taylm.boxMid B)))

noncomputable def Taylm.aux_goLoop (lb : (Fin n → Interval ℝ) → ℝ) (ub : Vec ℝ n → ℝ) :
    ℕ → List (Fin n → Interval ℝ) × ℝ → List (Fin n → Interval ℝ) × ℝ
  | 0, st => st
  | fuel + 1, st => Taylm.aux_goLoop lb ub fuel (Taylm.aux_goStep lb ub st)


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.globalMin (lb : (Fin n → Interval ℝ) → ℝ) (ub : Vec ℝ n → ℝ)
    (X : Fin n → Interval ℝ) (fuel : ℕ) : Interval ℝ :=
  let st := Taylm.aux_goLoop lb ub fuel ([X], ub (Taylm.boxMid X))
  ⟨min st.2 (Taylm.listMin lb st.1), st.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
