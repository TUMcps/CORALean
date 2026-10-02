import CORALean.ContDynamics.NonlinearARX.NonlinearARX

/-!
# Reading the output off the window

`y(k)` is block `0` of the window at step `k`; `outputSel` is the matrix that selects
it, as `LinearARX.outputEq`'s `C`, over `ℝ`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearARX.outputSel (_sys : NonlinearARX dy du p) : Mat ℝ dy (p * dy) :=
  Matrix.of fun r c =>
    if (finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
