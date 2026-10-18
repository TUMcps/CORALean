module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# DeepZ's S-shape band is sound when the derivative rises and then falls

[1, Fig. 2]: the parallelogram between the lines of slope `λ` through `(l, f(l))` and through
`(u, f(u))` encloses `f` on `[l, u]` once `λ ≤ min(f'(l), f'(u))`. That holds when `f'` rises up
to some `x'` and falls after it, which is `f'' ≥ 0` left of `x'` and `f'' ≤ 0` right of it, the
sigmoid's shape: `f'` then stays above its smaller end value on the box, so `f - λ x` does not
fall there, and its values at the two ends bound it. The paper's footnote prints the opposite
curvature; `deepZSShape_cube_not_sound` is what that gives.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem sShape_band_sound {f df : ℝ → ℝ} {x' lam l u t : ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hmono : MonotoneOn df (Set.Iic x'))
    (hanti : AntitoneOn df (Set.Ici x')) (hlam : lam ≤ min (df l) (df u))
    (hl : l ≤ t) (hu : t ≤ u) : -- --- STMT ---
    f l + lam * (t - l) ≤ f t ∧ f t ≤ f u + lam * (t - u) := by -- --- PROOF ---
  -- `f'` stays above its smaller end value on the box
  have hge : ∀ x, l ≤ x → x ≤ u → lam ≤ df x := fun x hlx hxu => by
    rcases le_total x x' with hx | hx
    · exact le_trans (le_trans hlam (min_le_left _ _))
        (hmono (le_trans hlx hx : l ≤ x') hx hlx)
    · exact le_trans (le_trans hlam (min_le_right _ _))
        (hanti hx (le_trans hx hxu : x' ≤ u) hxu)
  -- so `f - λ x` does not fall on `[l, u]`
  have hg : ∀ x, HasDerivAt (fun y => f y - lam * y) (df x - lam) x := fun x => by
    have hlin : HasDerivAt (fun y => lam * y) lam x := by
      simpa using (hasDerivAt_id x).const_mul lam
    exact (hd x).sub hlin
  have hmon : MonotoneOn (fun y => f y - lam * y) (Set.Icc l u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc l u)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg x).deriv]
    linarith [hge x hx.1.le hx.2.le]
  have h1 := hmon ⟨le_rfl, le_trans hl hu⟩ ⟨hl, hu⟩ hl
  have h2 := hmon ⟨hl, hu⟩ ⟨le_trans hl hu, le_rfl⟩ hu
  simp only at h1 h2
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
