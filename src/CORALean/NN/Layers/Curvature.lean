import CORALean.NN.Layers.Activation

/-!
# A slope out of a bound on the derivative

`Relaxation.ofMonotone` carries slope zero because monotonicity is all it has:
the range of `σ` over a box says nothing about how `σ` moves inside it. A slope
needs second-order information, and the cheapest form of it is a bracket
`m ≤ σ' ≤ M` over the box.

The mean value theorem is then the whole argument. Every increment of `σ` is
between `m` and `M` times the increment of its argument, so `σ t - λ t` stays
within `(M - m) (u - l)` of its value at `l`, and recentring halves that. The
error is quadratic in the box width wherever the bracket is — `M - m` shrinks
with the box — against the linear `(σ u - σ l) / 2` that monotonicity gives.
The theorem asks only what that argument uses: continuity on the closed box and
a derivative on the open one, so a kink at an endpoint costs nothing.

It is not the tight constant: the bracket alone allows a factor two better,
anchored at the midpoint, and four below that at the tangent point `σ' = λ`.

`Relaxation.ofAffineConj` needs none of this again, for an affine conjugate. -/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- The mean value theorem read as a bracket: with `m ≤ σ' ≤ M` over the box,
`σ t - lam * t` cannot leave the two ends the bracket allows. -/
theorem sub_mul_bounds_of_deriv {σ σ' : ℝ → ℝ} {m M lam l u t : ℝ}
    (hc : ContinuousOn σ (Set.Icc l u))
    (hd : ∀ x, l < x → x < u → HasDerivAt σ (σ' x) x)
    (hm : ∀ x, l ≤ x → x ≤ u → m ≤ σ' x) (hM : ∀ x, l ≤ x → x ≤ u → σ' x ≤ M)
    (hml : m ≤ lam) (hlM : lam ≤ M) (hl : l ≤ t) (hu : t ≤ u) :
    σ l - lam * l + (m - lam) * (u - l) ≤ σ t - lam * t
      ∧ σ t - lam * t ≤ σ l - lam * l + (M - lam) * (u - l) := by -- --- PROOF ---
  have hw : 0 ≤ u - l := by linarith
  rcases eq_or_lt_of_le hl with hlt | hlt
  · -- a box with `t` at its left end: both ends straddle zero, which is the claim
    subst hlt
    have h₁ : 0 ≤ (lam - m) * (u - l) := mul_nonneg (by linarith) hw
    have h₂ : 0 ≤ (M - lam) * (u - l) := mul_nonneg (by linarith) hw
    exact ⟨by linarith, by linarith⟩
  · have hcont : ContinuousOn σ (Set.Icc l t) := hc.mono (Set.Icc_subset_Icc le_rfl hu)
    obtain ⟨c, hcm, hceq⟩ := exists_hasDerivAt_eq_slope σ σ' hlt hcont
      fun x hx => hd x hx.1 (hx.2.trans_le hu)
    have hlow := hm c (le_of_lt hcm.1) (le_trans (le_of_lt hcm.2) hu)
    have hhigh := hM c (le_of_lt hcm.1) (le_trans (le_of_lt hcm.2) hu)
    rw [hceq] at hlow hhigh
    have hpos : 0 < t - l := by linarith
    -- the slope over `[l, t]` is in the bracket, so the increment is bracketed too
    rw [le_div_iff₀ hpos] at hlow
    rw [div_le_iff₀ hpos] at hhigh
    have hspan : t - l ≤ u - l := by linarith
    have hup : (M - lam) * (t - l) ≤ (M - lam) * (u - l) :=
      mul_le_mul_of_nonneg_left hspan (by linarith)
    have hdn : (m - lam) * (u - l) ≤ (m - lam) * (t - l) :=
      mul_le_mul_of_nonpos_left hspan (by linarith)
    exact ⟨by linarith, by linarith⟩

/-- The relaxation a derivative bracket buys. `lam` is free: it is clamped into
`[lo, hi]` by its own hypothesis, never checked against `σ`. -/
noncomputable def Relaxation.ofDeriv {σ σ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (lo hi lam : ℝ → ℝ → ℝ)
    (hlo : ∀ l u x, l ≤ x → x ≤ u → lo l u ≤ σ' x)
    (hhi : ∀ l u x, l ≤ x → x ≤ u → σ' x ≤ hi l u)
    (hlam : ∀ l u, l ≤ u → lo l u ≤ lam l u ∧ lam l u ≤ hi l u) : Relaxation σ where
  slope := lam
  offset l u := σ l - lam l u * l + ((lo l u + hi l u) / 2 - lam l u) * (u - l)
  error l u := (hi l u - lo l u) * (u - l) / 2
  sound {l u t} hl hu := by
    obtain ⟨h₁, h₂⟩ := sub_mul_bounds_of_deriv
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ _ => hd x)
      (hlo l u) (hhi l u)
      (hlam l u (le_trans hl hu)).1 (hlam l u (le_trans hl hu)).2 hl hu
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-- A relaxation of `f` transported along `g t = a f (b t) + c`, `0 < a`, `0 < b`.
Whatever built `R` carries over unchanged: `g`'s bracket at `l, u` is `f`'s at
`b l, b u`, rescaled. -/
noncomputable def Relaxation.ofAffineConj {f g : ℝ → ℝ} (R : Relaxation f) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hg : ∀ t, g t = a * f (b * t) + c) : Relaxation g where
  slope l u := a * b * R.slope (b * l) (b * u)
  offset l u := a * R.offset (b * l) (b * u) + c
  error l u := a * R.error (b * l) (b * u)
  sound {l u t} hl hu := by
    have hbl : b * l ≤ b * t := mul_le_mul_of_nonneg_left hl hb.le
    have hbu : b * t ≤ b * u := mul_le_mul_of_nonneg_left hu hb.le
    -- the affine map's own slope and offset cancel, leaving `a` times `f`'s deviation
    have heq : g t - (a * b * R.slope (b * l) (b * u) * t
        + (a * R.offset (b * l) (b * u) + c))
        = a * (f (b * t) - (R.slope (b * l) (b * u) * (b * t) + R.offset (b * l) (b * u))) := by
      rw [hg t]; ring
    rw [heq, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (R.sound hbl hbu) ha.le


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two relaxations of the same `σ`, the smaller error taken on each box. Both
are sound everywhere, so the choice costs nothing and buys precision. -/
noncomputable def Relaxation.tighter {σ : ℝ → ℝ} (R₁ R₂ : Relaxation σ) : Relaxation σ where
  slope l u := if R₁.error l u ≤ R₂.error l u then R₁.slope l u else R₂.slope l u
  offset l u := if R₁.error l u ≤ R₂.error l u then R₁.offset l u else R₂.offset l u
  error l u := if R₁.error l u ≤ R₂.error l u then R₁.error l u else R₂.error l u
  sound {l u _t} hl hu := by
    by_cases h : R₁.error l u ≤ R₂.error l u
    · rw [if_pos h, if_pos h, if_pos h]
      exact R₁.sound hl hu
    · rw [if_neg h, if_neg h, if_neg h]
      exact R₂.sound hl hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
