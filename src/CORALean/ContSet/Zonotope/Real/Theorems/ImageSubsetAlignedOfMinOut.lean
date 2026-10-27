module

public import CORALean.ContSet.Zonotope.Real.Operations.Aligned
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# A feasible point of (min-out) gives an aligned zonotope around `EW`

[1, Prop. 1]: `EW ⊆ ([α₁g₁, …, α_N g_N], c)` whenever `c + Σᵢ θᵢⱼ gᵢ = E wⱼ` at every
vertex `wⱼ` of `W` and `|θᵢⱼ| ≤ αᵢ`, the constraints of (min-out). That the point is
the *minimizer* is not used: any feasible point gives the inclusion, which is how
it is stated here, with `W` the convex hull of the vertices `V`.

(min-out) as printed ranges its constraint over `i = 0, 1, …, N`; there is no `g₀`,
and the index is read as `1, …, N`. The bound `αᵢ ≤ 1` is not needed for the inclusion.

## Inputs
* `Z` – zonotope
* `E` – linear map
* `V` – vertices
* `θ` – coefficient matrix
* `a` – generator scalings
* `c` – center

## Hypotheses
* `hθ` – coefficients bounded by the scalings
* `heq` – vertex images match the aligned generators

## Conclusion
* the image of the hull lies in the aligned zonotope

## References

* [1] [L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters,
      2022.](../../../../../../references/2022/yang-lcss-zonotopic-underapproximation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p M : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: a feasible point `(θ, α, c)` of (min-out) puts `E conv(V)` inside the
zonotope aligned with `Z` at `(c, α)`. -/
theorem Zonotope.image_subset_aligned_of_minOut (Z : Zonotope (Vec ℝ n)) (E : Mat ℝ n p)
    (V : Fin M → Vec ℝ p) (θ : Fin Z.h → Fin M → ℝ) (a : Fin Z.h → ℝ) (c : Vec ℝ n)
    (hθ : ∀ i j, |θ i j| ≤ a i) (heq : ∀ j, c + ∑ i, θ i j • Z.G i = E *ᵥ V j) : -- --- CONCL ---
    (E *ᵥ ·) '' convexHull ℝ (Set.range V) ⊆ (Z.aligned c a).construct := by -- --- PROOF ---
  show (Matrix.mulVecLin E) '' convexHull ℝ (Set.range V) ⊆ _
  rw [LinearMap.image_convexHull]
  refine convexHull_min ?_ (Zonotope.convex_construct _)
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  -- the coefficient of `αᵢgᵢ` is `θᵢⱼ/αᵢ`, and `0` where `αᵢ = 0` forces `θᵢⱼ = 0`
  refine ⟨fun i => if a i = 0 then 0 else θ i j / a i, fun i => ?_, ?_⟩
  · by_cases ha : a i = 0
    · simp [ha]
    · have hpos : 0 < a i := lt_of_le_of_ne ((abs_nonneg _).trans (hθ i j)) (Ne.symm ha)
      simp only [ha, if_false, abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).mpr (hθ i j)
  · have hterm : ∀ i, (if a i = 0 then 0 else θ i j / a i) • (Z.aligned c a).G i
        = θ i j • Z.G i := by
      intro i
      simp only [Zonotope.aligned, smul_smul]
      by_cases ha : a i = 0
      · have h0 : θ i j = 0 := abs_nonpos_iff.mp (ha ▸ hθ i j)
        simp [ha, h0]
      · rw [if_neg ha, div_mul_cancel₀ _ ha]
    simp only [Matrix.mulVecLin_apply, ← heq j, hterm]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
