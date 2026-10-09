import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachPolyFloat
import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.ContSet.HPolytope.Float.Theorems.MinkDiffOfInner

/-!
# The float eroded polytope is inside the exact one

[1, Alg. 2] lines 4-5 in floats keep `X ⊖ F box(X_end) ⊖ B_μ` from the inside, which is the
direction an inner approximation needs. Stated against the exact object, with the two things a
float run gets wrong on purpose bounded the right way: the float zonotope holds every point of the
exact `F box(X_end)` (an outer enclosure, which only shrinks a difference) and the float radius is
at least the exact `μ`. Each of the two differences is `HPolytope.minkDiffOf_inner`, whose
equality-row condition is asked of both subtrahends.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Lines 4-5 in floats are inside `X ⊖ F box(X_end) ⊖ B_μ` of the exact layer, for any exact
`F box(X_end)` the float zonotope holds and any exact `μ` the float one is above. -/
theorem LinearSys.maxBackReachPolyFloat_inner (p : ℕ) (X : HPolytope 𝕋 n) (FB : Zonotope 𝕋 n)
    (μ : 𝕋) {Fr : Set (Vec ℝ n)} {μr : ℝ} (hFr : Fr ⊆ FB.construct) (hμ : μr ≤ toReal μ)
    (hker₁ : ∀ i, ∀ y ∈ FB.construct, (toRealMat X.Ae *ᵥ y) i = 0)
    (hker₂ : ∀ i, ∀ y ∈ (Capsule.mk (fun _ => (zero : 𝕋)) (fun _ => zero)
      (maximum zero μ)).construct, (toRealMat X.Ae *ᵥ y) i = 0) :
    (LinearSys.maxBackReachPolyFloat p X FB μ).construct ⊆
      minkowskiDiff (minkowskiDiff X.construct Fr)
        (Real.Capsule.mk (0 : Vec ℝ n) 0 μr).construct := by -- --- PROOF ---
  intro x hx y hy z hz
  set ball : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, maximum zero μ⟩ with hball
  -- the exact ball sits inside the float one
  have hyball : y ∈ ball.construct := by
    -- the witness `t` is kept, the zero centre and segment vanish, the radius grows
    obtain ⟨t, ht, hle⟩ := hy
    have hc : ∀ i, toReal (ball.c i) = 0 := fun i => toReal_zero
    have hg : ∀ i, toReal (ball.g i) = 0 := fun i => toReal_zero
    have hr : toReal ball.r = max 0 (toReal μ) := by
      rw [hball]; show toReal (maximum zero μ) = _; rw [toReal_maximum, toReal_zero]
    refine ⟨t, ht, ?_⟩
    show Real.sqrt (∑ i, (y i - (toReal (ball.c i) + t * toReal (ball.g i))) ^ 2) ≤ toReal ball.r
    simp only [hc, hg, hr]
    have hle' : Real.sqrt (∑ i, y i ^ 2) ≤ μr := by simpa using hle
    simpa using le_trans hle' (le_trans hμ (le_max_right 0 (toReal μ)))
  have key : ∀ (P : HPolytope 𝕋 n) (T : Set (Vec ℝ n))
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
