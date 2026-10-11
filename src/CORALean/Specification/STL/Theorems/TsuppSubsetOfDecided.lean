import CORALean.Specification.STL.Definitions.Tsupp

/-!
# The time support lies in any set that decides the formula

[1, Eq. 12]: if the values of a trace on `T` settle `ϕ`, a change at a time outside `T` cannot
flip it, so `tsupp(ϕ) ⊆ T`. The converse, that `tsupp(ϕ)` itself decides `ϕ`, is not here.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12]: a set that decides `ϕ` contains its time support. -/
theorem STL.Formula.tsupp_subset_of_decided {φ : STL.Formula X} {T : Set ℝ≥0}
    (h : φ.DecidedOn T) : φ.tsupp ⊆ T := by
  rintro t ⟨ξ, ξ', hξ, hξ', hagree⟩
  by_contra ht
  -- the two traces agree on `T`, since they differ only at `t ∉ T`
  exact hξ' ((h ξ ξ' fun s hs => hagree s fun hst => ht (hst ▸ hs)).1 hξ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
