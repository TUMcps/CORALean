import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.diag`

CORA's `@interval/diag` on a vector: `interval(diag(I.inf), diag(I.sup))`, the diagonal
matrices over the box. The box has the point `0` off the diagonal. CORA's optional offset `k` is
not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A vector box as the box of diagonal matrices over it. -/
def Interval.diag (I : Interval (Vec ℝ n)) : Interval (Mat ℝ n n) where
  inf := Matrix.diagonal I.inf
  sup := Matrix.diagonal I.sup

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
