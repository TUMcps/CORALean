module

public import CORALean.ContSet.Taylm.Real.Operations.GoLoop
public import CORALean.ContSet.Taylm.Real.Operations.ListMin

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
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.globalMin (lb : (Fin n → ℝ × ℝ) → ℝ) (ub : Vec ℝ n → ℝ)
    (X : Fin n → ℝ × ℝ) (fuel : ℕ) : ℝ × ℝ :=
  let st := Taylm.goLoop lb ub fuel ([X], ub (Taylm.boxMid X))
  (min st.2 (Taylm.listMin lb st.1), st.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
