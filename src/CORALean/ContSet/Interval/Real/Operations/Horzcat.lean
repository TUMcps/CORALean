module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.horzcat`

CORA's `@interval/horzcat`: the two bound matrices are concatenated side by side. CORA's
`horzcat` takes any number of arguments, and a numeric argument is the point interval; it is
associative, so two operands are the whole content (a numeric matrix is `Interval.point`).

## Inputs
* `I` – left interval matrix
* `J` – right interval matrix

## Output
* interval matrix of the two side by side
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.horzcat (I : Interval (Mat ℝ m n₁)) (J : Interval (Mat ℝ m n₂)) :
    Interval (Mat ℝ m (n₁ + n₂)) where
  inf := fun i => Fin.append (I.inf i) (J.inf i)
  sup := fun i => Fin.append (I.sup i) (J.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
