module

public import CORALean.NN.Layers.Operations.CubeRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.Float.SqrtDownCoraLe

@[expose] public section

/-!
# The chord relaxation of the cube is sound

`g(x) = x³ - m x` has `g(a) - g(b) = (a - b)(a² + a b + b² - m)`. For `m ≤ 0` it rises, so on
`[l, u]` it lies between `g(l)` and `g(u)`. For `m > 0`, with `3 s² = m`, it rises outside
`[-s, s]` and falls inside, and `g(t) - g(∓s) = (t ± s)² (t ∓ 2 s)`: on the box it is at most the
larger of `g(u)` and `g` at `-s` clamped into the box, and at least the smaller of `g(l)` and `g` at
`s` clamped. The computed roots bracket `s`, clamping keeps the order, and `g` over the clamped
pair bounds `g` at the clamped point. The margin is not negative, so
`Relaxation.ofBand_enclosesWhere` concludes, on every box.

## Inputs
* `p` – the square root's Newton steps
* `w` – the margin's factor

## Hypotheses
* `hw` – the factor is not negative

## Conclusion
* the relaxation is sound for `x ↦ x³`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The difference of `g` at two points. -/
private theorem aux_diff (m a b : ℝ) :
    (a ^ 3 - m * a) - (b ^ 3 - m * b) = (a - b) * (a ^ 2 + a * b + b ^ 2 - m) := by
  ring

/-- `g` rises from `a` to `b` where both are at least `s`, or both at most `-s` (`m ≤ 3 s²`), or
anywhere for `m ≤ 0`. -/
private theorem aux_rise {m s a b : ℝ} (hm : m ≤ 3 * s ^ 2) (hs : 0 ≤ s) (hab : a ≤ b)
    (h : s ≤ a ∨ b ≤ -s ∨ m ≤ 0) : -- --- CONCL ---
    a ^ 3 - m * a ≤ b ^ 3 - m * b := by -- --- PROOF ---
  have hd := aux_diff m b a
  have hq : 0 ≤ b ^ 2 + b * a + a ^ 2 - m := by
    rcases h with h | h | h
    · nlinarith
    · nlinarith
    · nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hq]

/-- `g` falls from `a` to `b` inside `[-s, s]` (`3 s² ≤ m`). -/
private theorem aux_fall {m s a b : ℝ} (hm : 3 * s ^ 2 ≤ m) (hab : a ≤ b) (ha : -s ≤ a)
    (hb : b ≤ s) :
    b ^ 3 - m * b ≤ a ^ 3 - m * a := by
  have hd := aux_diff m a b
  have hq : a ^ 2 + a * b + b ^ 2 - m ≤ 0 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (neg_nonneg.mpr hq)]

/-- The real upper end: at most the larger of `g(u)` and `g(c)`, `c` the clamped `-s`. -/
private theorem aux_upper {m s l u t : ℝ} (hm : 3 * s ^ 2 = m) (hs : 0 ≤ s) (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
    t ^ 3 - m * t ≤ max (u ^ 3 - m * u)
      (min (max (-s) l) u ^ 3 - m * min (max (-s) l) u) := by -- --- PROOF ---
  rcases le_total s t with hst | hst
  · exact le_trans (aux_rise hm.ge hs hu (Or.inl hst)) (le_max_left _ _)
  rcases le_total t (-s) with hts | hts
  · rcases le_total u (-s) with hus | hus
    · exact le_trans (aux_rise hm.ge hs hu (Or.inr (Or.inl hus))) (le_max_left _ _)
    · -- the clamped point is `-s`, and `g(t) - g(-s) = (t + s)² (t - 2 s)`
      have hc : min (max (-s) l) u = -s := by
        rw [max_eq_left (le_trans hl hts)]; exact min_eq_left hus
      rw [hc]
      refine le_trans ?_ (le_max_right _ _)
      have hid : (t ^ 3 - m * t) - ((-s) ^ 3 - m * (-s)) = (t + s) ^ 2 * (t - 2 * s) := by
        rw [← hm]; ring
      nlinarith [mul_nonneg (sq_nonneg (t + s)) (by linarith : (0 : ℝ) ≤ 2 * s - t)]
  · -- inside: the clamped point is `max(-s, l) ≤ t`, and `g` falls from it to `t`
    have hc : min (max (-s) l) u = max (-s) l := min_eq_left (le_trans (max_le hts hl) hu)
    rw [hc]
    refine le_trans ?_ (le_max_right _ _)
    exact aux_fall hm.le (max_le hts hl) (le_max_left _ _) hst

/-- The real lower end: at least the smaller of `g(l)` and `g(q)`, `q` the clamped `s`. -/
private theorem aux_lower {m s l u t : ℝ} (hm : 3 * s ^ 2 = m) (hs : 0 ≤ s) (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
    min (l ^ 3 - m * l) (min (max s l) u ^ 3 - m * min (max s l) u) ≤
      t ^ 3 - m * t := by -- --- PROOF ---
  rcases le_total t (-s) with hts | hts
  · exact le_trans (min_le_left _ _) (aux_rise hm.ge hs hl (Or.inr (Or.inl hts)))
  rcases le_total s t with hst | hst
  · rcases le_total s l with hsl | hsl
    · exact le_trans (min_le_left _ _) (aux_rise hm.ge hs hl (Or.inl hsl))
    · -- the clamped point is `s`, and `g(t) - g(s) = (t - s)² (t + 2 s)`
      have hc : min (max s l) u = s := by
        rw [max_eq_left hsl]; exact min_eq_left (le_trans hst hu)
      rw [hc]
      refine le_trans (min_le_right _ _) ?_
      have hid : (t ^ 3 - m * t) - (s ^ 3 - m * s) = (t - s) ^ 2 * (t + 2 * s) := by
        rw [← hm]; ring
      nlinarith [mul_nonneg (sq_nonneg (t - s)) (by linarith : (0 : ℝ) ≤ t + 2 * s)]
  · -- inside: the clamped point is `min(s, u) ≥ t`, and `g` falls from `t` to it
    have hc : max s l = s := max_eq_left (le_trans hl hst)
    rw [hc]
    refine le_trans (min_le_right _ _) ?_
    exact aux_fall hm.le (le_min hst hu) hts (min_le_left _ _)

/-- `g` over `[a, b]` from above at a point of it, for `m ≥ 0`. -/
private theorem aux_pair_upper {m a b c : ℝ} (hm : 0 ≤ m) (hac : a ≤ c)
    (hcb : c ≤ b) : -- --- CONCL ---
    c ^ 3 - m * c ≤ b ^ 3 - m * a := by -- --- PROOF ---
  have h3 : c ^ 3 ≤ b ^ 3 := by
    have : b ^ 3 - c ^ 3 = (b - c) * (b ^ 2 + b * c + c ^ 2) := by ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hcb)
      (by nlinarith [sq_nonneg (b + c)] : (0 : ℝ) ≤ b ^ 2 + b * c + c ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left hac hm]

/-- `g` over `[a, b]` from below at a point of it, for `m ≥ 0`. -/
private theorem aux_pair_lower {m a b c : ℝ} (hm : 0 ≤ m) (hac : a ≤ c)
    (hcb : c ≤ b) : -- --- CONCL ---
    a ^ 3 - m * b ≤ c ^ 3 - m * c := by -- --- PROOF ---
  have h3 : a ^ 3 ≤ c ^ 3 := by
    have : c ^ 3 - a ^ 3 = (c - a) * (c ^ 2 + c * a + a ^ 2) := by ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hac)
      (by nlinarith [sq_nonneg (c + a)] : (0 : ℝ) ≤ c ^ 2 + c * a + a ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left hcb hm]

/-- The cube from above. -/
private theorem aux_cubeUp (x : 𝕋) : -- --- CONCL ---
    toReal x ^ 3 ≤ toReal (step_cubeUp x) := by -- --- PROOF ---
  unfold step_cubeUp
  rw [toReal_maximum]
  rcases le_total 0 (toReal x) with hx | hx
  · have h1 := mul_le_mulUp x x
    have h2 := mul_le_mulUp (mulUp x x) x
    refine le_trans ?_ (le_max_left _ _)
    nlinarith [mul_le_mul_of_nonneg_right h1 hx]
  · have h1 := mulDown_le_mul x x
    have h2 := mul_le_mulUp (mulDown x x) x
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [mul_le_mul_of_nonpos_right h1 hx]

/-- The cube from below. -/
private theorem aux_cubeDown (x : 𝕋) : -- --- CONCL ---
    toReal (step_cubeDown x) ≤ toReal x ^ 3 := by -- --- PROOF ---
  unfold step_cubeDown
  rw [toReal_minimum]
  rcases le_total 0 (toReal x) with hx | hx
  · have h1 := mulDown_le_mul x x
    have h2 := mulDown_le_mul (mulDown x x) x
    refine le_trans (min_le_left _ _) ?_
    nlinarith [mul_le_mul_of_nonneg_right h1 hx]
  · have h1 := mul_le_mulUp x x
    have h2 := mulDown_le_mul (mulUp x x) x
    refine le_trans (min_le_right _ _) ?_
    nlinarith [mul_le_mul_of_nonpos_right h1 hx]

/-- For `m > 0` the computed roots bracket `√(m / 3)`. -/
private theorem aux_roots (p : ℕ) (l u : 𝕋)
    (hm : 0 < toReal (step_cubeSlope l u)) : -- --- CONCL ---
    toReal (step_cubeRootDown p l u) ≤ Real.sqrt (toReal (step_cubeSlope l u) / 3) ∧
      Real.sqrt (toReal (step_cubeSlope l u) / 3) ≤ toReal
        (step_cubeRootUp p l u) := by -- --- PROOF ---
  set m := step_cubeSlope l u with hmdef
  constructor
  · -- `three` is at least 3, `1 / three` at most a third
    unfold step_cubeRootDown
    rw [← hmdef]
    dsimp only
    have h1 := add_le_addUp (one : 𝕋) one
    have h2 := add_le_addUp one (addUp (one : 𝕋) one)
    rw [toReal_one] at h1 h2
    have h3 : 3 ≤ toReal (addUp one (addUp (one : 𝕋) one)) := by linarith
    have hd := divDown_le_div one (addUp one (addUp (one : 𝕋) one)) (by linarith)
    rw [toReal_one] at hd
    -- so the radicand is at most `m / 3`
    have hthird : toReal (divDown one (addUp one (addUp (one : 𝕋) one))) ≤ 1 / 3 :=
      le_trans hd (one_div_le_one_div_of_le (by norm_num) h3)
    refine le_trans (sqrtDownCora_le p _) (Real.sqrt_le_sqrt ?_)
    have := mulDown_le_mul m (divDown one (addUp one (addUp (one : 𝕋) one)))
    nlinarith [mul_le_mul_of_nonneg_left hthird hm.le]
  · -- the third is at least a third
    unfold step_cubeRootUp
    rw [← hmdef]
    dsimp only
    set three := addDown one (addDown (one : 𝕋) one)
    set third : 𝕋 := if ltStrict zero three then divUp one three else one with hthird_def
    have hthird : 1 / 3 ≤ toReal third := by
      rw [hthird_def]
      split_ifs with h
      · have hp := toReal_lt_of_ltStrict h
        rw [toReal_zero] at hp
        have h1 := addDown_le_add (one : 𝕋) one
        have h2 := addDown_le_add one (addDown (one : 𝕋) one)
        rw [toReal_one] at h1 h2
        have hle : toReal three ≤ 3 := by linarith
        have hu := div_le_divUp one three hp
        rw [toReal_one] at hu
        exact le_trans (one_div_le_one_div_of_le hp hle) hu
      · rw [toReal_one]; norm_num
    -- so the radicand is at least `m / 3`
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtUp p _)
    have := mul_le_mulUp m third
    nlinarith [mul_le_mul_of_nonneg_left hthird hm.le]


-- =======================================  MAIN THEOREM  ======================================= --

theorem cubeRelaxation_encloses (p : ℕ) {w : 𝕋} (hw : 0 ≤ toReal w) : -- --- CONCL ---
    (cubeRelaxation p w).Encloses fun x => x ^ 3 := by -- --- PROOF ---
  have hW := Relaxation.ofBand_enclosesWhere (σ := fun x => x ^ 3) (P := fun _ _ => True)
    (s := step_cubeSlope) (lo := step_cubeLo p) (hi := step_cubeHi p) (b := step_cubeMargin w)
    (fun {l u t} _ hl hu => ?_) (fun {l u} _ => ?_)
  · exact ⟨fun hl hu => hW.sound trivial hl hu⟩
  · set m := step_cubeSlope l u with hmdef
    -- `g` over a pair, both ways, at any `m`
    have hpU : ∀ a b : 𝕋, toReal b ^ 3 - toReal m * toReal a ≤ toReal (step_cubeGUp m a b) := by
      intro a b
      have h1 := aux_cubeUp b
      have h2 := sub_le_subUp (step_cubeUp b) (mulDown m a)
      have h3 := mulDown_le_mul m a
      unfold step_cubeGUp
      linarith
    have hpD : ∀ a b : 𝕋, toReal (step_cubeGDown m a b) ≤ toReal a ^ 3 - toReal m * toReal b := by
      intro a b
      have h1 := aux_cubeDown a
      have h2 := subDown_le_sub (step_cubeDown a) (mulUp m b)
      have h3 := mul_le_mulUp m b
      unfold step_cubeGDown
      linarith
    -- the clamp, and the two ends as `min` and `max` of the four values
    have hc : ∀ x : 𝕋,
        toReal (step_cubeClamp l u x) = min (max (toReal x) (toReal l)) (toReal u) := by
      intro x
      unfold step_cubeClamp
      rw [toReal_minimum, toReal_maximum]
    have hlo : toReal (step_cubeLo p l u) ≤ min (min (toReal (step_cubeGDown m l l))
        (toReal (step_cubeGDown m u u))) (min (toReal (step_cubeGDown m
          (step_cubeClamp l u (step_cubeRootDown p l u)) (step_cubeClamp l u
            (step_cubeRootUp p l u)))) (toReal (step_cubeGDown m (step_cubeClamp l u
              (neg (step_cubeRootUp p l u))) (step_cubeClamp l u
                (neg (step_cubeRootDown p l u)))))) := by
      unfold step_cubeLo
      rw [← hmdef]
      dsimp only
      rw [toReal_minimum, toReal_minimum, toReal_minimum]
    -- the upper end as the `max` of the four values
    have hhi : max (max (toReal (step_cubeGUp m l l)) (toReal (step_cubeGUp m u u)))
        (max (toReal (step_cubeGUp m (step_cubeClamp l u (step_cubeRootDown p l u))
          (step_cubeClamp l u (step_cubeRootUp p l u)))) (toReal (step_cubeGUp m
            (step_cubeClamp l u (neg (step_cubeRootUp p l u))) (step_cubeClamp l u
              (neg (step_cubeRootDown p l u)))))) ≤ toReal (step_cubeHi p l u) := by
      unfold step_cubeHi
      rw [← hmdef]
      dsimp only
      rw [toReal_maximum, toReal_maximum, toReal_maximum]
    have hgl := hpD l l
    have hgu := hpU u u
    show toReal (step_cubeLo p l u) ≤ t ^ 3 - toReal m * t ∧
      t ^ 3 - toReal m * t ≤ toReal (step_cubeHi p l u)
    rcases le_or_gt (toReal m) 0 with hm | hm
    · -- `m ≤ 0`: `g` rises, between its ends
      have h1 := aux_rise (s := 0) (by linarith) le_rfl hl (Or.inr (Or.inr hm))
      have h2 := aux_rise (s := 0) (by linarith) le_rfl hu (Or.inr (Or.inr hm))
      constructor
      · exact le_trans hlo (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
          (by linarith)))
      · exact le_trans (by linarith) (le_trans (le_max_right _ _)
          (le_trans (le_max_left _ _) hhi))
    · -- `m > 0`: the stationary point `s`, bracketed by the two roots
      set s := Real.sqrt (toReal m / 3) with hsdef
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : 3 * s ^ 2 = toReal m := by
        rw [hsdef, Real.sq_sqrt (by linarith)]; ring
      obtain ⟨hra, hrb⟩ := aux_roots p l u hm
      rw [← hmdef, ← hsdef] at hra hrb
      set sa := step_cubeRootDown p l u
      set sb := step_cubeRootUp p l u
      constructor
      · -- below: `g(l)` or `g` at the clamped `s`, inside the clamped pair
        refine le_trans hlo (le_trans (min_le_min (le_trans (min_le_left _ _) hgl) ?_)
          (aux_lower hs2 hs0 hl hu))
        refine le_trans (min_le_left _ _) (le_trans (hpD _ _) ?_)
        rw [hc, hc]
        exact aux_pair_lower hm.le (min_le_min (max_le_max hra le_rfl) le_rfl)
          (min_le_min (max_le_max hrb le_rfl) le_rfl)
      · -- above: `g(u)` or `g` at the clamped `-s`, inside the clamped pair
        refine le_trans (aux_upper hs2 hs0 hl hu) (le_trans (max_le_max ?_ ?_) hhi)
        · exact le_trans hgu (le_max_right _ _)
        · refine le_trans ?_ (le_max_right _ _)
          refine le_trans ?_ (hpU _ _)
          rw [hc, hc, toReal_neg, toReal_neg]
          exact aux_pair_upper hm.le (min_le_min (max_le_max (neg_le_neg hrb) le_rfl) le_rfl)
            (min_le_min (max_le_max (neg_le_neg hra) le_rfl) le_rfl)
  · -- the margin: `max(|l|, |u|)³` rounded up is not negative
    unfold step_cubeMargin
    dsimp only
    set big := maximum (absolute l) (absolute u)
    have hk : 0 ≤ toReal big := by
      rw [toReal_maximum, toReal_absolute]; exact le_trans (abs_nonneg _) (le_max_left _ _)
    have h1 := mul_le_mulUp big big
    have h1' : 0 ≤ toReal (mulUp big big) := le_trans (mul_nonneg hk hk) h1
    have h2 := mul_le_mulUp (mulUp big big) big
    have h2' : 0 ≤ toReal (mulUp (mulUp big big) big) := le_trans (mul_nonneg h1' hk) h2
    have h3 := mul_le_mulUp (mulUp (mulUp big big) big) w
    nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
