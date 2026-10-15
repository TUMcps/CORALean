module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Operations.Project
public import CORALean.Specification.AtomicProposition.Operations.Basic

@[expose] public section

/-!
# Can an atomic proposition be true on a set

`out = canBeTrue(ap,set,loc)` of `atomicProposition.m`: false if the location is not allowed;
otherwise the set projected to `dims` is tested for an intersection with the proposition's set,
`isIntersecting_(ap.set,set,'exact',tol)`, and with `'approx'` when the exact algorithm throws
(`CORA:noops`, `CORA:noExactAlg`). The test is `IsDisjoint`, the negation of `isIntersecting_`:
`true` only if the two sets share no point, so `canBeTrue` is conservative towards `true`. Which
of the exact and the approximate algorithm runs, and the tolerance `tol = 1e-12`, are the
instance's: the guarantee holds for both.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = canBeTrue(ap,set,loc)`. -/
def AtomicProposition.canBeTrue (ap : AtomicProposition S n) (set : S n) (loc : ℕ) : Bool :=
  -- check if loc is contained at all
  if ap.containsLoc loc = false then false
  else
    -- if the set is intersecting with the proposition, it can be true
    let projected := ContSet.project (𝕋 := 𝕋) set ap.dims
    !IsDisjoint.isDisjoint ap.set projected

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
