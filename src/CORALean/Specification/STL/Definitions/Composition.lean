import CORALean.Specification.STL.STL

/-!
# Compositions of formulas

The functions `f(φ₁, …, φ_n)` of [1, Lemma 3]: `φᵢ` composed by `∧`, `∨` and `X_c`, written as a
syntax tree with `n` holes.

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

open scoped NNReal

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive STL.Comp (n : ℕ)
  | hole (i : Fin n)
  | and (f g : Comp n)
  | or (f g : Comp n)
  | next (c : ℝ≥0) (f : Comp n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
