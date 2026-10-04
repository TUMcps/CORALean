import CORALean.Specification.STL.Definitions.RTL

/-!
# Finally in RTL

`F[a,b] ψ := true U[a,b] ψ` of [1, Def. 2], with `true` as `A ⊤`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `F[a,b] ψ`. -/
def RTL.Formula.finally (a b : ℝ≥0) (ψ : RTL.Formula X) : RTL.Formula X :=
  .until a b (.A Pform.top) ψ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
