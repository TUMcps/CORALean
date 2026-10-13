module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.vertcat`

CORA's `@interval/vertcat`: the two bound matrices are stacked. CORA's `cat(dim, I₁, …)` is
`cat` of the two bound arrays; for `dim = 1` and `dim = 2` it is `vertcat` and `horzcat`
(higher `dim` are `n`-d arrays, which CORA's own `interval` methods mostly reject).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m₁ m₂ n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.vertcat (I : Interval (Mat ℝ m₁ n)) (J : Interval (Mat ℝ m₂ n)) :
    Interval (Mat ℝ (m₁ + m₂) n) where
  inf := Fin.append I.inf J.inf
  sup := Fin.append I.sup J.sup


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
