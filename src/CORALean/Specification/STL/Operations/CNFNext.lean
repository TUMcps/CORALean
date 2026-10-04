import CORALean.Specification.STL.Definitions.SampledTime

/-!
# The next-operator on a normal form

`X_c(⋁ⱼ X_c^j …) ≡ ⋁ⱼ X_c^{j+1} …`: [1, Sec. 4.1]'s `X_c(ϕ₁ ∨ ϕ₂) ≡ X_cϕ₁ ∨ X_cϕ₂` raises every
power.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every `j` raised by one. -/
def STL.CNF.next (a : STL.CNF X) : STL.CNF X :=
  a.map fun cl => cl.map fun b => { b with j := b.j + 1 }


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
