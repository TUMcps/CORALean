import CORALean.NN.Layers.Definitions.DeepZSShape
import CORALean.NN.Layers.Theorems.Real.SShapeBandSound

/-!
# DeepZ's S-shape transformer is sound, for the right S

[1, Thm. 3.2], corrected: Eq. (7) encloses `f` on every box when `f'` rises up to some `x'`
and falls after it. At `l = u` it is the constant `f(u)`; otherwise
`λ t + μ₁ ∓ μ₂` are the two lines of `sShape_band_sound` at `λ = min(f'(l), f'(u))`, through
`(l, f(l))` and `(u, f(u))`.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem deepZSShape_sound {f df : ℝ → ℝ} {x' : ℝ} (hd : ∀ x, HasDerivAt f (df x) x)
    (hmono : MonotoneOn df (Set.Iic x')) (hanti : AntitoneOn df (Set.Ici x')) :
    (deepZSShape f df).Sound f := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  change l ≤ t at hl
  change t ≤ u at hu
  show |f t - ((deepZSShape f df).slope l u * t + (deepZSShape f df).offset l u)|
    ≤ (deepZSShape f df).error l u
  by_cases hlu : l = u
  · -- a point: the constant `f(u)`, exactly
    subst hlu
    have ht : t = l := le_antisymm hu hl
    subst ht
    simp [deepZSShape]
  · -- the two lines of the band, recentred
    obtain ⟨h1, h2⟩ := sShape_band_sound (lam := min (df l) (df u)) hd hmono hanti le_rfl hl hu
    simp only [deepZSShape, if_neg hlu]
    rw [abs_le]
    constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
