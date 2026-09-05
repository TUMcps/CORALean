import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Layers.Curvature

/-!
# A slope out of a derivative bracket, over a floating-point scalar

`Real.sub_mul_bounds_of_deriv` is the whole mathematical content, and it is
about the exact `σ` and the exact reals the floats denote — so it is reused
here rather than restated. What this file adds is the rounding: the two ends it
gives are evaluated in floats, each pushed outward.

Only two products need care about which way they round. `(lo - lam)(u - l)` is a
non-positive factor times a non-negative one, so the *widest* second factor
makes it smallest; `(hi - lam)(u - l)` has both factors non-negative, so the
widest makes it largest. Both take `subUp u l`, for opposite reasons.

Nothing constrains `lam`, exactly as in `Activation`: a caller passing a clamped
guess owes only that the clamp lands in the bracket, which `minimum` and
`maximum` give exactly. The error is measured from the ends actually stored.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}

/-- The lower end of `σ t - lam t` over the box, rounded down. -/
private def curvLo (E : Enclosure 𝕋 σ) (lo lam : 𝕋 → 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 :=
  addDown (subDown (E.lo l) (mulUp (lam l u) l))
    (mulDown (subDown (lo l u) (lam l u)) (subUp u l))

/-- The upper end, rounded up. -/
private def curvHi (E : Enclosure 𝕋 σ) (hi lam : 𝕋 → 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 :=
  addUp (subUp (E.hi l) (mulDown (lam l u) l))
    (mulUp (subUp (hi l u) (lam l u)) (subUp u l))

/-- Any float between the two ends would do; the midpoint is the one that makes
the error smallest, and its own rounding costs nothing. -/
private def curvMid (E : Enclosure 𝕋 σ) (lo hi lam : 𝕋 → 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 :=
  half (addUp (curvLo E lo lam l u) (curvHi E hi lam l u))

/-- The relaxation a derivative bracket buys, over a floating-point scalar. The
bracket, the slope and `σ` at the left end all arrive as floats. -/
def Relaxation.ofDeriv (σ' : ℝ → ℝ) (hd : ∀ x, HasDerivAt σ (σ' x) x) (E : Enclosure 𝕋 σ)
    (lo hi lam : 𝕋 → 𝕋 → 𝕋)
    (hlo : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u → toReal (lo l u) ≤ σ' x)
    (hhi : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u → σ' x ≤ toReal (hi l u))
    (hlam : ∀ l u : 𝕋, toReal l ≤ toReal u →
      toReal (lo l u) ≤ toReal (lam l u) ∧ toReal (lam l u) ≤ toReal (hi l u)) :
    Relaxation 𝕋 σ where
  slope := lam
  offset := curvMid E lo hi lam
  -- the distance to whichever end is further, so the offset's own rounding is paid for
  error l u := maximum (subUp (curvHi E hi lam l u) (curvMid E lo hi lam l u))
    (subUp (curvMid E lo hi lam l u) (curvLo E lo lam l u))
  sound {l u t} hl hu := by
    have hle : toReal l ≤ toReal u := le_trans hl hu
    obtain ⟨hlow, hhigh⟩ := Real.sub_mul_bounds_of_deriv hd (hlo l u) (hhi l u)
      (hlam l u hle).1 (hlam l u hle).2 hl hu
    have hwidth := sub_le_subUp u l
    have hA : toReal (curvLo E lo lam l u) ≤ σ t - toReal (lam l u) * t := by
      have hfac := subDown_le_sub (lo l u) (lam l u)
      have hfac0 : toReal (subDown (lo l u) (lam l u)) ≤ 0 := by
        have := (hlam l u hle).1
        linarith
      -- a non-positive factor against the widest box: the smallest the product can be
      have hstep : toReal (subDown (lo l u) (lam l u)) * toReal (subUp u l)
          ≤ (toReal (lo l u) - toReal (lam l u)) * (toReal u - toReal l) :=
        le_trans (mul_le_mul_of_nonpos_left hwidth hfac0)
          (mul_le_mul_of_nonneg_right hfac (by linarith))
      have hprod := mulDown_le_mul (subDown (lo l u) (lam l u)) (subUp u l)
      have hint := subDown_le_sub (E.lo l) (mulUp (lam l u) l)
      have hmul := mul_le_mulUp (lam l u) l
      have hend := E.lo_le l
      have hsum := addDown_le_add (subDown (E.lo l) (mulUp (lam l u) l))
        (mulDown (subDown (lo l u) (lam l u)) (subUp u l))
      rw [curvLo]
      linarith
    have hB : σ t - toReal (lam l u) * t ≤ toReal (curvHi E hi lam l u) := by
      have hfac := sub_le_subUp (hi l u) (lam l u)
      have hfac0 : 0 ≤ toReal (subUp (hi l u) (lam l u)) := by
        have := (hlam l u hle).2
        linarith
      -- both factors non-negative here, so the widest box makes the product largest
      have hstep : (toReal (hi l u) - toReal (lam l u)) * (toReal u - toReal l)
          ≤ toReal (subUp (hi l u) (lam l u)) * toReal (subUp u l) :=
        le_trans (mul_le_mul_of_nonneg_right hfac (by linarith))
          (mul_le_mul_of_nonneg_left hwidth hfac0)
      have hprod := mul_le_mulUp (subUp (hi l u) (lam l u)) (subUp u l)
      have hint := sub_le_subUp (E.hi l) (mulDown (lam l u) l)
      have hmul := mulDown_le_mul (lam l u) l
      have hend := E.le_hi l
      have hsum := add_le_addUp (subUp (E.hi l) (mulDown (lam l u) l))
        (mulUp (subUp (hi l u) (lam l u)) (subUp u l))
      rw [curvHi]
      linarith
    have hspread := abs_sub_le_spread (c := curvMid E lo hi lam l u) hA hB
    rw [show σ t - (toReal (lam l u) * t + toReal (curvMid E lo hi lam l u))
      = σ t - toReal (lam l u) * t - toReal (curvMid E lo hi lam l u) from by ring]
    exact hspread

/-- Two relaxations of the same `σ`, the smaller error taken on each box. `le`
is unconstrained and does not have to be: both branches are sound, so a wrong
answer costs precision and never soundness. -/
def Relaxation.tighter (R₁ R₂ : Relaxation 𝕋 σ) : Relaxation 𝕋 σ where
  slope l u := if le (R₁.error l u) (R₂.error l u) then R₁.slope l u else R₂.slope l u
  offset l u := if le (R₁.error l u) (R₂.error l u) then R₁.offset l u else R₂.offset l u
  error l u := if le (R₁.error l u) (R₂.error l u) then R₁.error l u else R₂.error l u
  sound {l u _t} hl hu := by
    by_cases h : le (R₁.error l u) (R₂.error l u) = true
    · rw [if_pos h, if_pos h, if_pos h]
      exact R₁.sound hl hu
    · rw [if_neg h, if_neg h, if_neg h]
      exact R₂.sound hl hu

end CORALean.Float
