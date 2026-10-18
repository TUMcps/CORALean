module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachPolyFloat
public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.InflatedContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.HPolytope.Float.Theorems.MinkDiffOfInner

@[expose] public section

/-!
# The float eroded polytope is inside the exact one

[1, Alg. 3] lines 4-5 in floats keep `X ⊖ F box(X_end) ⊖ B_μ` from the inside, which is the
direction an inner approximation needs. Stated against the exact object, with the two things a
float run gets wrong on purpose bounded the right way: the float zonotope holds every point of the
exact `F box(X_end)` (an outer enclosure, which only shrinks a difference) and the float radius is
at least the exact `μ`. Each of the two differences is `HPolytope.minkDiffOf_inner`, whose
equality-row condition is asked of both subtrahends.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Lines 4-5 in floats are inside `X ⊖ F box(X_end) ⊖ B_μ` of the exact layer, for any exact
`F box(X_end)` the float zonotope holds and any exact `μ` the float one is above. -/
theorem LinearSys.maxBackReachPolyFloat_inner (p : ℕ) (X : HPolytope 𝕋 (Vec 𝕋 n))
    (FB : Zonotope (Vec 𝕋 n))
    (μ : 𝕋) {Fr : Set (Vec ℝ n)} {μr : ℝ} (hFr : Fr ⊆ FB.construct) (hμ : μr ≤ toReal μ)
    (hker₁ : ∀ i, ∀ y ∈ FB.construct, (toRealMat X.Ae *ᵥ y) i = 0)
    (hker₂ : ∀ i, ∀ y ∈ (Capsule.mk (fun _ => (zero : 𝕋)) (fun _ => zero) (maximum zero μ)
      (Interval.origin n)).construct, (toRealMat X.Ae *ᵥ y) i = 0) : -- --- STMT ---
    (LinearSys.maxBackReachPolyFloat p X FB μ).construct ⊆
      minkowskiDiff (minkowskiDiff X.construct Fr)
        (Real.Capsule.mk (0 : Vec ℝ n) 0 μr).construct := by -- --- PROOF ---
  intro x hx y hy z hz
  set ball : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, maximum zero μ, Interval.origin n⟩
    with hball
  -- the exact ball sits inside the float one
  have hyball : y ∈ ball.construct := by
    -- the witness `t` is kept, the zero center and segment vanish, the radius grows
    obtain ⟨t, ht, hle⟩ := hy
    have hc : ∀ i, toReal (ball.c i) = 0 := fun i => toReal_zero
    have hg : ∀ i, toReal (ball.g i) = 0 := fun i => toReal_zero
    have hr : toReal ball.r = max 0 (toReal μ) := by
      rw [hball]; show toReal (maximum zero μ) = _; rw [toReal_maximum, toReal_zero]
    -- the box is the origin, so the nominal ball is in the float one
    refine InflatedContSet.nominalSet_subset_construct ?_ ⟨t, ht, ?_⟩
    · show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
      rw [Interval.origin_exact]
      rfl
    show Real.sqrt (∑ i, (y i - (toReal (ball.c i) + t * toReal (ball.g i))) ^ 2) ≤ toReal ball.r
    simp only [hc, hg, hr]
    have hle' : Real.sqrt (∑ i, y i ^ 2) ≤ μr := by simpa using hle
    simpa using le_trans hle' (le_trans hμ (le_max_right 0 (toReal μ)))
  -- each difference keeps a point plus its subtrahend in the polytope
  have key : ∀ (P : HPolytope 𝕋 (Vec 𝕋 n)) (T : Set (Vec ℝ n))
      (u : ∀ i, FloatBound 𝕋 T (rowLin P.A i)) (x : Vec ℝ n),
      x ∈ (P.minkDiffOf T u).construct →
      (∀ i, ∀ y ∈ T, (toRealMat P.Ae *ᵥ y) i = 0) → ∀ y ∈ T, x + y ∈ P.construct :=
    fun P T u x hx hk y hy => HPolytope.minkDiffOf_inner P T u hk hx y hy
  unfold LinearSys.maxBackReachPolyFloat at hx
  have h2 := key _ _ _ x hx hker₂ y hyball
  have h1 := key _ _ _ _ h2 hker₁ z (hFr hz)
  exact h1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
