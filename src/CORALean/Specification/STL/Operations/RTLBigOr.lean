import CORALean.Specification.STL.Definitions.RTL

/-!
# A disjunction of RTL formulas

The `⋁` of a list of RTL formulas, as in [1, Lemma 2], Eq. (17). RTL has no `false`: the empty `⋁`
is `A ⊥`, false of every reach sequence with a state at `0`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⋁` of a list. -/
def RTL.Formula.bigOr (l : List (RTL.Formula X)) : RTL.Formula X := l.foldr .or (.A .bot)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
