import CORALean.Specification.STL.Definitions.ReachSequence

/-!
# The traces of a system lie in the traces of its reach sequence

[1, Eq. 1]: `C(R)` contains the set of traces `Traces(S)` when `R` is a reach sequence of it,
the first half of the remark after Eq. 1.

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

theorem ReachSequence.traces_subset_traceSet {R : ℝ≥0 → Set X} {Traces : Set (ℝ≥0 → X)}
    (h : ReachSequence.Encloses R Traces) : Traces ⊆ ReachSequence.traceSet R :=
  fun ξ hξ t => h t ξ hξ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
