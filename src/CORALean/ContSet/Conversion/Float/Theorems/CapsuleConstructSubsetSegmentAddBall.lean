module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleConstructEqSegmentAddBall
public import CORALean.ContSet.Ellipsoid.Float.Theorems.BallContains
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A float capsule lies in its segment plus its ball

The float layer's form of `Capsule.construct_eq_segment_add_ball`: the segment `zonotope(c, g)`
takes the capsule's error box along, and the ball is `Ellipsoid.ball`, whose shape is rounded up
(`Ellipsoid.ball_contains`). A negative stored radius denotes the empty capsule.

## Inputs
* `C` – capsule

## Hypotheses
* none

## Conclusion
* capsule is contained in segment plus ball
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float capsule lies in its segment, with the error box, plus the float ball. -/
theorem Capsule.construct_subset_segment_add_ball (C : Capsule 𝕋 n) :
    C.construct ⊆ (⟨1, C.c, fun _ => C.g, C.I_error⟩ : Zonotope (Vec 𝕋 n)).construct
      + (Ellipsoid.ball n C.r).construct := by -- --- PROOF ---
  rintro x ⟨y, hy, e, he, rfl⟩
  -- the nominal capsule is empty at a negative radius
  have hr : 0 ≤ toReal C.r := by
    by_contra h
    have hempty := Real.Capsule.construct_eq_empty (C := C.nominal) (lt_of_not_ge h)
    exact (Set.eq_empty_iff_forall_notMem.mp hempty) y hy
  -- otherwise the nominal capsule is its segment plus its ball, over ℝ
  have hy' : y ∈ C.nominal.construct := hy
  rw [Real.Capsule.construct_eq_segment_add_ball C.nominal hr] at hy'
  obtain ⟨s, hs, b, hb, rfl⟩ := hy'
  refine ⟨s + e, ⟨s, hs, e, he, rfl⟩, b, Ellipsoid.ball_contains C.r hb, ?_⟩
  exact add_right_comm s e b

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
