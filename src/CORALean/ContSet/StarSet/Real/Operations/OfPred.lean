module

public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A predicate as a star set

The star set with center `0`, the unit vectors as basis and `p` as the predicate: the coefficients
are the point, so it denotes what `p` denotes (`Theorems/OfPredExact`). Any set a representation
of the family denotes is a star set this way, which is how [1, Def. 1] generalizes them.

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p` as a star set: center `0`, the identity basis, predicate `p`. -/
def StarSet.ofPred {P : ℕ → Type} {n : ℕ} (p : P n) : StarSet P n where
  m := n
  c := 0
  G := fun i k => if i = k then 1 else 0
  pred := p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
