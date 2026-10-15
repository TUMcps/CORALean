module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.NormType`: the norms `intervalMatrix.norm` accepts

CORA's `norm(intMat, type)` takes `1`, `Inf` or `'fro'`: the maximum absolute column sum, the
maximum absolute row sum and the Frobenius norm. `type = 2` is refused (the exact value over
the box is NP-hard) and has no constructor.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The matrix norms of MATLAB's `norm(A, type)` that `intervalMatrix.norm` supports. -/
inductive Interval.NormType where
  | one
  | inf
  | fro

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
