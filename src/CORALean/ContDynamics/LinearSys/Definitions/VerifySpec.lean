module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.Specification.Specification

@[expose] public section

/-!
# `Alg. 3`'s specification

The specification [1, Alg. 3] verifies on a set `X` of states: `X` inside every safe set
`G j` and disjoint from every unsafe set `F j`.

## Inputs
* `G` – safe polytopes
* `F` – unsafe polytopes
* `X` – set to check

## Output
* proposition that the set satisfies every safe and unsafe set

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X` satisfies every safe set `G j` and every unsafe set `F j`. -/
def LinearSys.VerifySpec (G : Fin (r + 1) → HPolytope (Vec ℝ n))
    (F : Fin (w + 1) → HPolytope (Vec ℝ n)) (X : Set (Vec ℝ n)) : Prop :=
  (∀ j, (Specification.safeSet (G j)).Holds X) ∧ ∀ j, (Specification.unsafeSet (F j)).Holds X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
