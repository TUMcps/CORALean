module

public import CORALean.NN.Layers.Operations.ApproxArea
public import CORALean.NN.Layers.Definitions.ApproxError
public import CORALean.NN.Layers.Definitions.DeepZSShape
public import CORALean.NN.Layers.Definitions.SecantSlope
public import CORALean.NN.Layers.Theorems.Real.SShapeBandSound

@[expose] public section

/-!
# The approximation area is at most Singh's

[1, Prop. 11]: for an S-shaped `ϕ` on `[l, u]`, with `[e, ē]` the approximation errors of the secant
[1, Def. 6, Def. 7] and `e_S` the error of Singh's enclosure [2, Thm. 3.2], `area([e, ē], [l, u]) ≤
area([-e_S, e_S], [l, u])`. The S-shape is the class of the tree's `deepZSShape_encloses`: the
derivative rises up to some `x'` and falls after it (the sigmoid, tanh); not the footnote's of [2,
Thm. 3.2], which is the wrong curvature. It gives `ϕ' ≥ m_S = min(ϕ'(l), ϕ'(u))` on `[l, u]`, which
is all the proof uses. The paper takes the two extrema in a figure; here every pair is bounded,
`g(x) - g(y) ≤ 2 e_S` for `g = ϕ - m x`.

## Inputs
* `ϕ` – S-shaped activation function
* `dϕ` – its derivative
* `x'` – turning point of the derivative
* `l` – lower end of the interval
* `u` – upper end of the interval

## Hypotheses
* `hd` – the activation has the given derivative
* `hmono` – derivative rises up to the turning point
* `hanti` – derivative falls after the turning point
* `hlu` – interval is ordered

## Conclusion
* the secant approximation's area is at most DeepZ's

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../../references/2025/koller-tmlr-set-based-training.md)
* [2] [G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". Advances in Neural Information Processing Systems,
      2018.](../../../../../../references/2018/singh-neurips-deepz.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem approxArea_le {ϕ dϕ : ℝ → ℝ} {x' : ℝ} (hd : ∀ x, HasDerivAt ϕ (dϕ x) x)
    (hmono : MonotoneOn dϕ (Set.Iic x')) (hanti : AntitoneOn dϕ (Set.Ici x')) (l u : ℝ)
    (hlu : l ≤ u) : -- --- CONCL ---
    approxArea (approxErrorLow ϕ (fun x => secantSlope ϕ l u * x) l u)
        (approxErrorUp ϕ (fun x => secantSlope ϕ l u * x) l u) l u ≤
      approxArea (-(deepZSShape ϕ dϕ).error l u)
        ((deepZSShape ϕ dϕ).error l u) l u := by -- --- PROOF ---
  rcases eq_or_lt_of_le hlu with rfl | hlt
  · simp [approxArea]
  set mS : ℝ := min (dϕ l) (dϕ u) with hmS
  set m : ℝ := secantSlope ϕ l u with hm
  have hne : l ≠ u := hlt.ne
  have herr : (deepZSShape ϕ dϕ).error l u = (ϕ u - ϕ l - mS * (u - l)) / 2 := by
    simp [deepZSShape, hne, hmS]
  -- `ϕ' ≥ m_S` on the box, so `ϕ(y) - ϕ(x) ≥ m_S (y - x)` for `x ≤ y` in it
  have hge : ∀ x ∈ Set.Icc l u, mS ≤ min (dϕ x) (dϕ x) := fun x hx => by
    rw [min_self]
    rcases le_total x x' with h | h
    · exact le_trans (min_le_left _ _) (hmono (le_trans hx.1 h : l ≤ x') h hx.1)
    · exact le_trans (min_le_right _ _) (hanti h (le_trans h hx.2 : x' ≤ u) hx.2)
  have hpair : ∀ x ∈ Set.Icc l u, ∀ y ∈ Set.Icc l u, x ≤ y → ϕ x + mS * (y - x) ≤ ϕ y := by
    intro x hx y hy hxy
    have hlam : mS ≤ min (dϕ x) (dϕ y) :=
      le_min (by simpa using hge x hx) (by simpa using hge y hy)
    exact (sShape_band_sound hd hmono hanti hlam hxy le_rfl).1
  -- the secant slope is at least `m_S`, and `(u - l) m = ϕ(u) - ϕ(l)`
  have hmu : (u - l) * m = ϕ u - ϕ l := by
    rw [hm, secantSlope]; field_simp
  have hmm : mS ≤ m := by
    have h := hpair l ⟨le_rfl, hlu⟩ u ⟨hlu, le_rfl⟩ hlu
    by_contra hcon
    push Not at hcon
    nlinarith [hmu, mul_lt_mul_of_pos_left hcon (sub_pos.mpr hlt)]
  -- every pair of values of `g = ϕ - m x` differs by at most `2 e_S`
  have hpairg : ∀ x ∈ Set.Icc l u, ∀ y ∈ Set.Icc l u,
      (ϕ x - m * x) - (ϕ y - m * y) ≤ ϕ u - ϕ l - mS * (u - l) := by
    intro x hx y hy
    rcases le_total y x with hyx | hxy
    · -- `y ≤ x`: `ϕ(x) ≤ ϕ(u) - m_S (u - x)`, `ϕ(y) ≥ ϕ(l) + m_S (y - l)`
      have h1 := hpair x hx u ⟨hlu, le_rfl⟩ hx.2
      have h2 := hpair l ⟨le_rfl, hlu⟩ y hy hy.1
      nlinarith [mul_le_mul_of_nonneg_right hmm (sub_nonneg.mpr hyx)]
    · -- `x ≤ y`: `ϕ(y) - ϕ(x) ≥ m_S (y - x)` and `y - x ≤ u - l`
      have h1 := hpair x hx y hy hxy
      nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub hy.2 hx.1) (sub_nonneg.mpr hmm)]
  -- so `ē ≤ e + 2 e_S`
  have hbound : approxErrorUp ϕ (fun x => secantSlope ϕ l u * x) l u ≤
      approxErrorLow ϕ (fun x => secantSlope ϕ l u * x) l u + (ϕ u - ϕ l - mS * (u - l)) := by
    unfold approxErrorUp
    refine csSup_le ⟨_, l, ⟨le_rfl, hlu⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    unfold approxErrorLow
    have : (fun x => ϕ x - (fun x => secantSlope ϕ l u * x) x) x -
        (ϕ u - ϕ l - mS * (u - l)) ≤ sInf ((fun x => ϕ x - (fun x => secantSlope ϕ l u * x) x) ''
          Set.Icc l u) := by
      refine le_csInf ⟨_, l, ⟨le_rfl, hlu⟩, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      have := hpairg x hx y hy
      simp only [hm] at this ⊢
      linarith
    linarith
  unfold approxArea
  rw [herr]
  nlinarith [mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hlu)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
