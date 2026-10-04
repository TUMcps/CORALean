import CORALean.Specification.STL.Definitions.Pform

/-!
# Sampled time formulas

[1, Sec. 4.1]: `ϕ := ϱ | ¬ϕ | ϕ₁ ∨ ϕ₂ | X_c ϕ | F(0,c) ϱ | G(0,c) ϱ`, with `∧` too, which the
rewriting of [1, Table 1] produces.

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

inductive STL.Samp (X : Type)
  | lit (ϱ : Pform X)
  | not (s : Samp X)
  | and (s t : Samp X)
  | or (s t : Samp X)
  | next (s : Samp X)
  | fin (ϱ : Pform X)
  | glob (ϱ : Pform X)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
