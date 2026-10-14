module

public import CORALean.ContSet.Capsule.Float.Operations.BoundDotUp
public import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# `Alg. 3` lines 4-5 in floats: the eroded polytope

`maxBackReachPoly` computed in `𝕋`: [1, Alg. 3] lines 4-5, `X ⊖ F box(X_end) ⊖ B_μ`, one of the
two polytopes of the inner approximated homogeneous time-interval solution (21). A difference
is a guarantee, so this is where the float layer rounds **inward**: each inequality's bound is
lowered by the subtrahend's support in that row's direction, rounded *up*
(`HPolytope.minkDiffOf` takes the certificates and subtracts them rounded down), so the
result is inside the exact difference. The first subtrahend, `F box(X_end)`, is the float
zonotope an outer enclosure hands in — larger than the exact one, which shrinks the result
further; the second, `B_μ`, is the ball of radius `max(0, μ)`.

The supports are computed, not supplied: the zonotope's through `ConZonotope.boundDot` (a
check in ℚ, hence `ToRat 𝕋`), the ball's through `Capsule.boundDotUp` with `p` Newton steps
for the root.

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

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-5: `X ⊖ F box(X_end) ⊖ B_μ`, inside the exact difference. -/
def LinearSys.maxBackReachPolyFloat (p : ℕ) (X : HPolytope 𝕋 (Vec 𝕋 n))
    (FB : Zonotope (Vec 𝕋 n)) (μ : 𝕋) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  let ball : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, maximum zero μ⟩   -- B_μ
  let XF := X.minkDiffOf FB.construct fun i =>                      -- ⊖ F box(X_end)
    let u := FB.conZonotope.boundDot (c := rowLin X.A i) (X.A i) fun _ => rfl
    ⟨u.val, fun x hx => u.le x (Zonotope.conZonotope_contains FB hx)⟩
  XF.minkDiffOf ball.construct fun i =>                             -- ⊖ B_μ
    ball.boundDotUp (f := rowLin XF.A i) (XF.A i) (fun _ => rfl) p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
