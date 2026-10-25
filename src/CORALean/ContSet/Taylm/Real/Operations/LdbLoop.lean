module

public import CORALean.ContSet.Taylm.Real.Operations.LdbStep
public import CORALean.ContSet.Taylm.Real.Operations.Reexpand

@[expose] public section

/-!
# The linear dominated bounder's iteration

[1, Sec. 2], step (3): on the current box, re-expanded at its center (step (1)), take a step; if
`d > ε` (a), shrink to the kept part and repeat, otherwise (b) `M` is the lower bound of the
minimum. The source repeats until (b); here `fuel` bounds the repetitions, and `M` is returned
when it runs out.

## Inputs
* `T` – Taylor model
* `ε` – gap tolerance

## Output
* lower bound of the model's minimum from the iteration

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.ldbLoop (T : Taylm n) (ε : ℝ) : ℕ → (Fin n → Interval ℝ) → ℝ
  | 0, B => (T.reexpand B).ldbStep.1.inf
  | fuel + 1, B =>
    -- (1)-(3) on the current box, re-expanded at its center
    let st := (T.reexpand B).ldbStep
    -- (a): `d > ε`, so shrink to the kept part and go to (3); (b): `M` is the bound
    if ε < st.1.sup - st.1.inf then
      Taylm.ldbLoop T ε fuel fun k => ⟨Taylm.boxMid B k + Taylm.boxRad B k * (st.2 k).inf,
        Taylm.boxMid B k + Taylm.boxRad B k * (st.2 k).sup⟩
    else st.1.inf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
