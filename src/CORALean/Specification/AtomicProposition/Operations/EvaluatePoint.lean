module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Specification.AtomicProposition.Operations.Basic

@[expose] public section

/-!
# Evaluating an atomic proposition at a point

`out = evaluatePoint(ap,point,loc)` of `atomicProposition.m`: whether the location is allowed and
the set contains the projection `point(ap.dims)` of the point. The point is given in the scalar
`𝕋` the trajectory is stored in, and `contains(ap.set,point)` is `Contains` at the singleton of
that point (`OfScalarPoint`), so the test is conservative like every `Contains`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]
  [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = evaluatePoint(ap,point,loc)`. -/
def AtomicProposition.evaluatePoint (ap : AtomicProposition S n) (point : Vec 𝕋 n) (loc : ℕ) :
    Bool :=
  ap.containsLoc loc && Contains.contains ap.set (OfScalarPoint.ofVec (S := S) (ap.readPoint point))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
