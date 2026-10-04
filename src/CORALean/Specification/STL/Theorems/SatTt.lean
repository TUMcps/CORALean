import CORALean.Specification.STL.STL

/-!
# `true` in STL

Every trace satisfies `true`, the `true` of [1, Sec. 2.2]'s `F` and `X`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_tt (ξ : ℝ≥0 → X) : (STL.Formula.tt : STL.Formula X).Sat ξ := by
  trivial

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
