module

public import CORALean.Specification.AtomicProposition.Definitions.Holds
public import CORALean.Specification.AtomicProposition.Operations.EvaluatePoint

@[expose] public section

/-!
# `evaluatePoint` is sound

If `evaluatePoint` says a point satisfies the proposition, it does: the location is allowed and
the coordinates `dims` of the point, read as reals, lie in the proposition's set. `false` claims
nothing, the `Contains` test being conservative.

## Inputs
* `ap` – atomic proposition
* `point` – floating-point point
* `loc` – location

## Hypotheses
* `h` – `evaluatePoint` returns true

## Conclusion
* the point, read as reals, satisfies the proposition
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]
  [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem AtomicProposition.evaluatePoint_sound (ap : AtomicProposition S n) (point : Vec 𝕋 n)
    (loc : ℕ) (h : ap.evaluatePoint point loc = true) : -- --- CONCL ---
    ap.Holds (toRealVec point) loc := by -- --- PROOF ---
  unfold AtomicProposition.evaluatePoint at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  -- the point is in its own singleton, which the set contains
  have hm := OfScalarPoint.mem_ofVec (S := S) (ap.readPoint point)
  have hsub := Contains.contains_sound _ _ h.2
  have : toRealVec (ap.readPoint point) = ap.readPoint (toRealVec point) := by
    funext i
    simp [AtomicProposition.readPoint, toRealVec_apply]
  rw [← this]
  exact hsub hm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
