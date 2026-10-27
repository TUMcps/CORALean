module

public import CORALean.NN.Layers.Definitions.DeepZSShape
public import CORALean.NN.Layers.Definitions.IsSShapedPrinted
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
# DeepZ's S-shape transformer is unsound for an S-shaped function as printed

[1, Thm. 3.2] as printed is false. `f(x) = x³` is smooth and monotone, and S-shaped by the
footnote, `f''(x) = 6x ≤ 0 ⇔ x ≤ 0`. On `[-1, 2]`, Eq. (7) gives `λ = min(3, 12) = 3`,
`μ₁ = (8 - 1 - 3 · 1) / 2 = 2` and `μ₂ = (8 + 1 - 3 · 3) / 2 = 0`, the line `3 x + 2` with no
width, which misses `f(1) = 1` by `4`: `f'` dips below both end values inside the box, the
curvature being the reverse of the sigmoid's. The same input breaks CORA's `'singh'` order-1
branch of `computeApproxPoly`, which takes Eq. (7) for every activation declared monotone,
`nnActLayerFromHandle(@(x) x.^3, [], 1)` among them, and returns `d = μ₂` unchecked.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the cube is S-shaped as printed and monotone, yet the transformer is unsound for it

## References

* [1] [G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". Advances in Neural Information Processing Systems,
      2018.](../../../../../../references/2018/singh-neurips-deepz.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem deepZSShape_cube_not_encloses : -- --- CONCL ---
    IsSShapedPrinted (fun x : ℝ => x ^ 3) ∧ Monotone (fun x : ℝ => x ^ 3)
      ∧ ¬ (deepZSShape (fun x : ℝ => x ^ 3) (deriv fun x : ℝ => x ^ 3)).Encloses
        (fun x : ℝ => x ^ 3) := by -- --- PROOF ---
  -- `f' = 3 x²` and `f'' = 6 x`
  have hd : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 :=
    funext fun x => by rw [(hasDerivAt_pow 3 x).deriv]; norm_num
  have hdd : deriv (fun x : ℝ => 3 * x ^ 2) = fun x => 6 * x :=
    funext fun x => by
      have := (HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_pow 2 x)).deriv
      simp only [Nat.cast_ofNat] at this
      rw [this]
      ring
  refine ⟨⟨ContDiff.pow contDiff_id 3, fun x => by rw [hd]; positivity, 0, fun x => ?_⟩,
    (show Odd 3 by decide).strictMono_pow.monotone, fun h => ?_⟩
  · rw [hd, hdd]
    constructor <;> intro hx <;> linarith
  · -- on `[-1, 2]` the band is the line `3 x + 2`, and `f(1) = 1` is off it
    have h1 := h.sound (l := (-1 : ℝ)) (u := 2) (t := 1)
      (by exact (by norm_num : (-1 : ℝ) ≤ 1)) (by exact (by norm_num : (1 : ℝ) ≤ 2))
    change |(1 : ℝ) ^ 3 - ((deepZSShape (fun x : ℝ => x ^ 3) (deriv fun x : ℝ => x ^ 3)).slope
      (-1) 2 * 1 + (deepZSShape (fun x : ℝ => x ^ 3) (deriv fun x : ℝ => x ^ 3)).offset (-1) 2)|
      ≤ (deepZSShape (fun x : ℝ => x ^ 3) (deriv fun x : ℝ => x ^ 3)).error (-1) 2 at h1
    simp only [deepZSShape, hd] at h1
    norm_num at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
