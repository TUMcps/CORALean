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

`Relaxation.ofAffineConj` below transports one along an affine conjugation
instead, rounding where the exact-real version needs no slack at all. -/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

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
    obtain ⟨hlow, hhigh⟩ := Real.sub_mul_bounds_of_deriv
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ _ => hd x)
      (hlo l u) (hhi l u) (hlam l u hle).1 (hlam l u hle).2 hl hu
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

/-! ## An affine conjugation

`g t = ra f (rb t) + c`, `ra, rb > 0` real. `FloatOps` fixes no format and no
numeral, so no float is guaranteed to denote `ra` or `rb` exactly — the caller
instead supplies a sound rounding of "multiply by `ra`" as two total functions,
`ScaleRounding`. For tanh's `ra = rb = 2` that rounding is `fun x => addUp x x`,
exact in any binary format and needing no float that denotes `2` at all. `c`,
an additive shift, is an ordinary float: `subUp`/`subDown` are what its own
rounding costs elsewhere, no pair needed.

The price this transport pays that the exact-real one does not: `t` is bounded
only by the box, so the gap between the two roundings of `ra * rb * R.slope`
is charged against `absolute`'s bound on `t`, not against nothing. -/

variable {f g : ℝ → ℝ}

/-- A sound rounding of multiplication by the fixed positive real `r`, as two
total functions rather than a stored float. -/
structure ScaleRounding (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (r : ℝ) where
  up : 𝕋 → 𝕋
  down : 𝕋 → 𝕋
  up_ge (x : 𝕋) : r * toReal x ≤ toReal (up x)
  down_le (x : 𝕋) : toReal (down x) ≤ r * toReal x

variable {ra rb : ℝ}

/-- Where `f`'s relaxation is read: `rb`'s rounding applied to each end. -/
private def confL (B : ScaleRounding 𝕋 rb) (l : 𝕋) : 𝕋 := B.down l

private def confU (B : ScaleRounding 𝕋 rb) (u : 𝕋) : 𝕋 := B.up u

private theorem confL_le (B : ScaleRounding 𝕋 rb) (hb : 0 ≤ rb) {l : 𝕋} {t : ℝ}
    (hl : toReal l ≤ t) : toReal (confL B l) ≤ rb * t :=
  le_trans (B.down_le l) (mul_le_mul_of_nonneg_left hl hb)

private theorem le_confU (B : ScaleRounding 𝕋 rb) (hb : 0 ≤ rb) {u : 𝕋} {t : ℝ}
    (hu : t ≤ toReal u) : rb * t ≤ toReal (confU B u) :=
  le_trans (mul_le_mul_of_nonneg_left hu hb) (B.up_ge u)

/-- The two roundings of `ra * rb * R.slope`, `rb`'s box map folded in first. -/
private def conjSlopeLow (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (l u : 𝕋) : 𝕋 :=
  A.down (B.down (R.slope (confL B l) (confU B u)))

private def conjSlopeHigh (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (l u : 𝕋) : 𝕋 :=
  A.up (B.up (R.slope (confL B l) (confU B u)))

-- `ra ≥ 0` is what lets the outer rounding preserve the inner one's direction
private theorem conjSlopeLow_le (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra)
    (B : ScaleRounding 𝕋 rb) (ha : 0 ≤ ra) (l u : 𝕋) :
    toReal (conjSlopeLow R A B l u)
      ≤ ra * rb * toReal (R.slope (confL B l) (confU B u)) := by -- --- PROOF ---
  rw [conjSlopeLow]
  calc toReal (A.down (B.down (R.slope (confL B l) (confU B u))))
      ≤ ra * toReal (B.down (R.slope (confL B l) (confU B u))) :=
        A.down_le (B.down (R.slope (confL B l) (confU B u)))
    _ ≤ ra * (rb * toReal (R.slope (confL B l) (confU B u))) :=
        mul_le_mul_of_nonneg_left (B.down_le (R.slope (confL B l) (confU B u))) ha
    _ = ra * rb * toReal (R.slope (confL B l) (confU B u)) := by ring

-- the mirrored bound, both roundings now the widening `up` direction
private theorem le_conjSlopeHigh (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra)
    (B : ScaleRounding 𝕋 rb) (ha : 0 ≤ ra) (l u : 𝕋) :
    ra * rb * toReal (R.slope (confL B l) (confU B u))
      ≤ toReal (conjSlopeHigh R A B l u) := by -- --- PROOF ---
  rw [conjSlopeHigh]
  calc ra * rb * toReal (R.slope (confL B l) (confU B u))
      = ra * (rb * toReal (R.slope (confL B l) (confU B u))) := by ring
    _ ≤ ra * toReal (B.up (R.slope (confL B l) (confU B u))) :=
        mul_le_mul_of_nonneg_left (B.up_ge (R.slope (confL B l) (confU B u))) ha
    _ ≤ toReal (A.up (B.up (R.slope (confL B l) (confU B u)))) :=
        A.up_ge (B.up (R.slope (confL B l) (confU B u)))

/-- The two roundings of `ra * R.offset + c`. Addition needs no sign
hypothesis, so these hold for any `ra`. -/
private def conjOffsetLow (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (c l u : 𝕋) : 𝕋 :=
  addDown (A.down (R.offset (confL B l) (confU B u))) c

private def conjOffsetHigh (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (c l u : 𝕋) : 𝕋 :=
  addUp (A.up (R.offset (confL B l) (confU B u))) c

private theorem conjOffsetLow_le (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra)
    (B : ScaleRounding 𝕋 rb) (c l u : 𝕋) :
    toReal (conjOffsetLow R A B c l u)
      ≤ ra * toReal (R.offset (confL B l) (confU B u)) + toReal c := by
  rw [conjOffsetLow]
  have h1 := A.down_le (R.offset (confL B l) (confU B u))
  have h2 := addDown_le_add (A.down (R.offset (confL B l) (confU B u))) c
  linarith

-- the mirrored bound, no sign hypothesis needed here either
private theorem le_conjOffsetHigh (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra)
    (B : ScaleRounding 𝕋 rb) (c l u : 𝕋) :
    ra * toReal (R.offset (confL B l) (confU B u)) + toReal c
      ≤ toReal (conjOffsetHigh R A B c l u) := by
  rw [conjOffsetHigh]
  have h1 := A.up_ge (R.offset (confL B l) (confU B u))
  have h2 := add_le_addUp (A.up (R.offset (confL B l) (confU B u))) c
  linarith

/-- A bound on `t` from the box alone, `l` and `u` not assumed of one sign. -/
private def conjTBound (l u : 𝕋) : 𝕋 := maximum (absolute l) (absolute u)

private theorem abs_le_conjTBound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |t| ≤ toReal (conjTBound l u) := by -- --- PROOF ---
  rw [conjTBound, toReal_maximum, toReal_absolute, toReal_absolute, abs_le]
  have hnl : -toReal l ≤ |toReal l| := by rw [← abs_neg]; exact le_abs_self _
  have hnu : toReal u ≤ |toReal u| := le_abs_self _
  refine ⟨?_, ?_⟩
  · have := le_max_left |toReal l| |toReal u|
    linarith
  · have := le_max_right |toReal l| |toReal u|
    linarith

/-- The slope and offset chosen: the midpoint of the interval either rounding
could land in, exactly as `curvMid` picks one above. -/
private def conjSlope (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (l u : 𝕋) : 𝕋 :=
  half (addUp (conjSlopeLow R A B l u) (conjSlopeHigh R A B l u))

private def conjOffset (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (c l u : 𝕋) : 𝕋 :=
  half (addUp (conjOffsetLow R A B c l u) (conjOffsetHigh R A B c l u))

private def conjSlopeGap (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (l u : 𝕋) : 𝕋 :=
  maximum (subUp (conjSlopeHigh R A B l u) (conjSlope R A B l u))
    (subUp (conjSlope R A B l u) (conjSlopeLow R A B l u))

private def conjOffsetGap (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (c l u : 𝕋) : 𝕋 :=
  maximum (subUp (conjOffsetHigh R A B c l u) (conjOffset R A B c l u))
    (subUp (conjOffset R A B c l u) (conjOffsetLow R A B c l u))

/-- `ra`'s own error, rounded up, plus the slope gap charged against `|t|`,
plus the offset gap. -/
private def conjError (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra) (B : ScaleRounding 𝕋 rb)
    (c l u : 𝕋) : 𝕋 :=
  addUp (addUp (A.up (R.error (confL B l) (confU B u)))
    (mulUp (conjSlopeGap R A B l u) (conjTBound l u))) (conjOffsetGap R A B c l u)

/-- `g t = ra f (rb t) + c` inherits `f`'s relaxation. The price for storing
one slope rather than the exact product is `conjSlopeGap` charged against a
bound on `t` itself. -/
noncomputable def Relaxation.ofAffineConj (R : Relaxation 𝕋 f) (A : ScaleRounding 𝕋 ra)
    (B : ScaleRounding 𝕋 rb) (c : 𝕋) (ha : 0 < ra) (hb : 0 < rb)
    (hg : ∀ t, g t = ra * f (rb * t) + toReal c) : Relaxation 𝕋 g where
  slope := conjSlope R A B
  offset := conjOffset R A B c
  error := conjError R A B c
  sound {l u t} hl hu := by
    have hbl := confL_le B hb.le hl
    have hbu := le_confU B hb.le hu
    have hRsound := R.sound hbl hbu
    -- the affine map's own slope and offset cancel, leaving `ra` times `f`'s deviation
    have heq : g t - (ra * rb * toReal (R.slope (confL B l) (confU B u)) * t
        + (ra * toReal (R.offset (confL B l) (confU B u)) + toReal c))
        = ra * (f (rb * t)
            - (toReal (R.slope (confL B l) (confU B u)) * (rb * t)
              + toReal (R.offset (confL B l) (confU B u)))) := by
      rw [hg t]; ring
    have hbound1 : |g t - (ra * rb * toReal (R.slope (confL B l) (confU B u)) * t
        + (ra * toReal (R.offset (confL B l) (confU B u)) + toReal c))|
        ≤ ra * toReal (R.error (confL B l) (confU B u)) := by
      rw [heq, abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left hRsound ha.le
    have hSlopeLow := conjSlopeLow_le R A B ha.le l u
    have hSlopeHigh := le_conjSlopeHigh R A B ha.le l u
    have hOffsetLow := conjOffsetLow_le R A B c l u
    have hOffsetHigh := le_conjOffsetHigh R A B c l u
    -- how far the chosen slope and offset can be from the exact product and sum
    have hSlopeGap : |ra * rb * toReal (R.slope (confL B l) (confU B u))
        - toReal (conjSlope R A B l u)| ≤ toReal (conjSlopeGap R A B l u) := by
      rw [conjSlopeGap]; exact abs_sub_le_spread hSlopeLow hSlopeHigh
    have hOffsetGap : |(ra * toReal (R.offset (confL B l) (confU B u)) + toReal c)
        - toReal (conjOffset R A B c l u)| ≤ toReal (conjOffsetGap R A B c l u) := by
      rw [conjOffsetGap]; exact abs_sub_le_spread hOffsetLow hOffsetHigh
    have htBound := abs_le_conjTBound hl hu
    -- the slope gap multiplies `t`, bounded only by the box, not by anything smaller
    have hcorrection : |(ra * rb * toReal (R.slope (confL B l) (confU B u))
        - toReal (conjSlope R A B l u)) * t|
        ≤ toReal (mulUp (conjSlopeGap R A B l u) (conjTBound l u)) := by
      rw [abs_mul]
      have hnn : (0:ℝ) ≤ toReal (conjSlopeGap R A B l u) := le_trans (abs_nonneg _) hSlopeGap
      exact le_trans (mul_le_mul hSlopeGap htBound (abs_nonneg t) hnn) (mul_le_mulUp _ _)
    -- the goal splits into the three pieces just bounded, plus their own roundings
    have hkey : g t - (toReal (conjSlope R A B l u) * t + toReal (conjOffset R A B c l u))
        = (g t - (ra * rb * toReal (R.slope (confL B l) (confU B u)) * t
            + (ra * toReal (R.offset (confL B l) (confU B u)) + toReal c)))
          + (ra * rb * toReal (R.slope (confL B l) (confU B u))
              - toReal (conjSlope R A B l u)) * t
          + ((ra * toReal (R.offset (confL B l) (confU B u)) + toReal c)
              - toReal (conjOffset R A B c l u)) := by ring
    rw [hkey]
    have htri1 := abs_add_le (g t - (ra * rb
        * toReal (R.slope (confL B l) (confU B u)) * t
        + (ra * toReal (R.offset (confL B l) (confU B u)) + toReal c))
      + (ra * rb * toReal (R.slope (confL B l) (confU B u))
          - toReal (conjSlope R A B l u)) * t)
      ((ra * toReal (R.offset (confL B l) (confU B u)) + toReal c)
          - toReal (conjOffset R A B c l u))
    -- the same split, one level in: the first two pieces against each other
    have htri2 := abs_add_le (g t - (ra * rb
        * toReal (R.slope (confL B l) (confU B u)) * t
        + (ra * toReal (R.offset (confL B l) (confU B u)) + toReal c)))
      ((ra * rb * toReal (R.slope (confL B l) (confU B u))
          - toReal (conjSlope R A B l u)) * t)
    have hstep1 := add_le_addUp (A.up (R.error (confL B l) (confU B u)))
      (mulUp (conjSlopeGap R A B l u) (conjTBound l u))
    have hstep2 := add_le_addUp (addUp (A.up (R.error (confL B l) (confU B u)))
      (mulUp (conjSlopeGap R A B l u) (conjTBound l u))) (conjOffsetGap R A B c l u)
    have hErrRound := A.up_ge (R.error (confL B l) (confU B u))
    rw [conjError]
    linarith [hbound1, hcorrection, hOffsetGap, htri1, htri2, hstep1, hstep2, hErrRound]


-- =====================================  MAIN DEFINITION  ====================================== --

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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
