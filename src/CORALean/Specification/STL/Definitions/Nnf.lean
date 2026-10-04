import CORALean.Specification.STL.Definitions.Pform

/-!
# STL formulas in negation normal form

[1, Lemma 4]: `ϕ` "without loss of generality" in negation normal form, built from non-temporal
literals `ϱ` (closed under `¬`) by `∧`, `∨`, `U[i,j]` and `R[i,j]`. The bounds are natural
numbers: a `c`-divisible formula is one scaled by `c`, which is what [1, Table 1]'s `c = 1` is.

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

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive STL.Nnf (X : Type)
  | lit (ϱ : Pform X)
  | and (φ ψ : Nnf X)
  | or (φ ψ : Nnf X)
  | until (i j : ℕ) (φ ψ : Nnf X)
  | release (i j : ℕ) (φ ψ : Nnf X)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
