module

public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A predicate as a star set

The star set with center `0`, the unit vectors as basis, the box `D` and `p` as the predicate: the
coefficients are the point, so it denotes what `p` denotes in `D` (`Theorems/OfPredExact`). Any
bounded set a representation of the family denotes is a star set this way, `D` any box around it,
which is how [1, Def. 1] generalizes them.

## Inputs
* `P` – predicate family
* `n` – dimension
* `D` – box of the factors
* `p` – predicate

## Output
* the star set of the points in `D` satisfying `p`

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p` on the box `D` as a star set: center `0`, the identity basis, predicate `p`. -/
def StarSet.ofPred {P : ℕ → Type} {n : ℕ} (D : Interval (Vec ℝ n)) (p : P n) :
    StarSet P n where
  m := n
  c := 0
  G := fun i k => if i = k then 1 else 0
  dom := D
  pred := p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
