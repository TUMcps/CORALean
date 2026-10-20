module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Operations.Project
public import CORALean.Specification.AtomicProposition.Operations.Basic

@[expose] public section

/-!
# Can an atomic proposition be false on a set

`out = canBeFalse(ap,set,loc)` of `atomicProposition.m`: the set projected to `dims` is tested for
containment in the proposition's set, `contains(ap.set,set)` and with `'approx'` when the exact
algorithm throws; the proposition can be false if the location is not allowed or the set is not
shown to be contained. The test is `Contains`, which is conservative (`true` only if the set is
contained), so `canBeFalse` is conservative towards `true`. Which algorithm runs is the instance's.

## Inputs
* `ap` – atomic proposition
* `set` – set to test
* `loc` – location

## Output
* whether the proposition can be false on the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = canBeFalse(ap,set,loc)`. -/
def AtomicProposition.canBeFalse (ap : AtomicProposition S n) (set : S n) (loc : ℕ) : Bool :=
  -- if the set is not enclosed by the proposition, it can be false
  let projected := ContSet.project (𝕋 := 𝕋) set ap.dims
  !ap.containsLoc loc || !Contains.contains ap.set projected

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
