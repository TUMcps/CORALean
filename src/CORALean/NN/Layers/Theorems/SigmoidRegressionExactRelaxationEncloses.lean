module

public import CORALean.NN.Layers.Operations.SigmoidRegressionExactRelaxation
public import CORALean.NN.Layers.Theorems.Real.EqPmArtanhOfSigmoidDeriv
public import CORALean.NN.Layers.Theorems.Real.ExistsCriticalExtreme
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.Real.SigmoidMono
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureEncloses

@[expose] public section

/-!
# The sigmoid relaxation with the exact error is sound

Whatever slope `m` the floats gave, `σ t - m t` on a box has its extremes at an end or where
`σ' = m` (Fermat), and there `σ' = m` puts the point at `±2 artanh √(1 - 4 m)` and `m` in
`(0, 1/4]`. The candidates are boxes: each end, and the float interval around each stationary
point, on which `σ t - m t` is bounded by monotonicity of `σ`. A stationary point inside the box is
inside its candidate, so the largest and smallest bound enclose the range, which the offset and
the error recenter.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the sigmoid
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `2⁻ʲ` is exactly what `j` halvings of one leave. -/
private theorem aux_toReal_halfIter (j : ℕ) : toReal (half^[j] (one : 𝕋)) = 1 / 2 ^ j := by
  induction j with
  | zero => simp [toReal_one]
  | succ j ih => rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ]; field_simp

/-- The upper bound of a box holds at every point of it, for every slope. -/
private theorem aux_extremumUp {E : Enclosure 𝕋} (hE : E.Encloses Real.sigmoid) (m a b : 𝕋)
    {t : ℝ} (ha : toReal a ≤ t) (hb : t ≤ toReal b) : -- --- CONCL ---
    Real.sigmoid t - toReal m * t ≤ toReal (step_extremumUp E m a b) := by -- --- PROOF ---
  have h1 : Real.sigmoid t ≤ toReal (E.enclose b).sup :=
    le_trans (Real.sigmoid_mono hb) (hE.le_hi b)
  have h2 : toReal (minimum (mulDown m a) (mulDown m b)) ≤ toReal m * t := by
    rw [toReal_minimum]
    rcases le_total 0 (toReal m) with h | h
    · exact le_trans (min_le_left _ _)
        (le_trans (mulDown_le_mul m a) (mul_le_mul_of_nonneg_left ha h))
    · exact le_trans (min_le_right _ _)
        (le_trans (mulDown_le_mul m b) (mul_le_mul_of_nonpos_left hb h))
  have h3 := sub_le_subUp (E.enclose b).sup (minimum (mulDown m a) (mulDown m b))
  unfold step_extremumUp
  linarith

/-- The lower bound of a box holds at every point of it, for every slope. -/
private theorem aux_extremumLo {E : Enclosure 𝕋} (hE : E.Encloses Real.sigmoid) (m a b : 𝕋)
    {t : ℝ} (ha : toReal a ≤ t) (hb : t ≤ toReal b) : -- --- CONCL ---
    toReal (step_extremumLo E m a b) ≤ Real.sigmoid t - toReal m * t := by -- --- PROOF ---
  have h1 : toReal (E.enclose a).inf ≤ Real.sigmoid t :=
    le_trans (hE.lo_le a) (Real.sigmoid_mono ha)
  have h2 : toReal m * t ≤ toReal (maximum (mulUp m a) (mulUp m b)) := by
    rw [toReal_maximum]
    rcases le_total 0 (toReal m) with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hb h)
        (le_trans (mul_le_mulUp m b) (le_max_right _ _))
    · exact le_trans (mul_le_mul_of_nonpos_left ha h)
        (le_trans (mul_le_mulUp m a) (le_max_left _ _))
  have h3 := subDown_le_sub (E.enclose a).inf (maximum (mulUp m a) (mulUp m b))
  unfold step_extremumLo
  linarith

/-- The lower bound of the stationary point is under `2 artanh √(1 - 4 m)`. -/
private theorem aux_stationaryLo_le (k : ℕ) (m : 𝕋) (hm : 0 < toReal m) : -- --- CONCL ---
    toReal (step_stationaryLo k m) ≤ 2 * Real.artanh (√(1 - 4 * toReal m)) := by -- --- PROOF ---
  have hs0 : 0 ≤ √(1 - 4 * toReal m) := Real.sqrt_nonneg _
  have hs1 : √(1 - 4 * toReal m) < 1 := by rw [Real.sqrt_lt' one_pos]; nlinarith
  unfold step_stationaryLo
  dsimp only
  split_ifs with hg
  · -- the capped root from below is under the root and inside `(-1, 1)`
    set x := minimum (subDown one (half^[52] one))
      (maximum zero (sqrtDown k (subDown one (nsmulUp 4 m)))) with hx
    -- the radicand rounded down is under `1 - 4 m`, so the root is under the real one
    have hv : toReal (subDown one (nsmulUp 4 m)) ≤ 1 - 4 * toReal m := by
      have h1 := subDown_le_sub (one : 𝕋) (nsmulUp 4 m)
      have h2 := le_nsmulUp 4 m
      rw [toReal_one] at h1
      push_cast at h2
      linarith
    have hxs : toReal x ≤ √(1 - 4 * toReal m) := by
      rw [hx, toReal_minimum, toReal_maximum, toReal_zero]
      exact le_trans (min_le_right _ _) (max_le hs0
        (le_trans (sqrtDown_le k _) (Real.sqrt_le_sqrt hv)))
    -- the cap leaves `1 - x` at least `2⁻⁵²`
    have hcap : toReal (subDown (one : 𝕋) (half^[52] one)) ≤ 1 - 1 / 2 ^ 52 := by
      have := subDown_le_sub (one : 𝕋) (half^[52] one)
      rwa [toReal_one, aux_toReal_halfIter] at this
    have hxc : toReal x ≤ 1 - 1 / 2 ^ 52 := by
      rw [hx, toReal_minimum]; exact le_trans (min_le_left _ _) hcap
    -- the guard puts `x` inside `(-1, 1)`
    have hneg : 0 < toReal (subDown one (neg x)) := by
      have := toReal_lt_of_ltStrict hg
      rwa [toReal_zero] at this
    have hneg' : -1 < toReal x := by
      have := subDown_le_sub (one : 𝕋) (neg x)
      rw [toReal_one, toReal_neg] at this
      linarith
    -- so `atanhDown` applies, its ratio being at most `2⁵³ ≤ 2⁶³`
    have hA := atanhDown_le 64 k x (by linarith [show (0 : ℝ) < 1 / 2 ^ 52 by positivity])
      hneg (fun hx0 => by
        rw [div_le_iff₀ (by linarith [show (0 : ℝ) < 1 / 2 ^ 52 by positivity])]
        have : (1 : ℝ) / 2 ^ 52 * 2 ^ 63 = 2 ^ 11 := by norm_num
        nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ^ 52 ≤ 1 - toReal x by linarith)
          (show (0 : ℝ) ≤ 2 ^ 63 by positivity)])
    have hB := Real.artanh_le_artanh hneg' hs1 hxs
    have hC := addDown_le_add (atanhDown 64 k x) (atanhDown 64 k x)
    linarith
  · rw [toReal_zero]; linarith [Real.artanh_nonneg hs0]

/-- The upper bound of the stationary point, where there is one, is above `2 artanh √(1 - 4 m)`. -/
private theorem aux_le_stationaryHi (k : ℕ) (m h : 𝕋) (hm : 0 < toReal m) (hm4 : toReal m ≤ 1 / 4)
    (hh : step_stationaryHi k m = some h) : -- --- CONCL ---
    2 * Real.artanh (√(1 - 4 * toReal m)) ≤ toReal h := by -- --- PROOF ---
  have hs0 : 0 ≤ √(1 - 4 * toReal m) := Real.sqrt_nonneg _
  unfold step_stationaryHi at hh
  dsimp only at hh
  split_ifs at hh with hg
  cases hh
  -- the radicand rounded up is above `1 - 4 m`, so the root is above the real one
  have hv : 1 - 4 * toReal m ≤ toReal (subUp one (nsmulDown 4 m)) := by
    have h1 := sub_le_subUp (one : 𝕋) (nsmulDown 4 m)
    have h2 := nsmulDown_le 4 m
    rw [toReal_one] at h1
    push_cast at h2
    linarith
  have hss : √(1 - 4 * toReal m) ≤ toReal (sqrtUp k (subUp one (nsmulDown 4 m))) :=
    le_trans (Real.sqrt_le_sqrt hv) (le_sqrtUp k _)
  -- the guard puts the root below one
  have hpos : 0 < toReal (subDown one (sqrtUp k (subUp one (nsmulDown 4 m)))) := by
    have := toReal_lt_of_ltStrict hg
    rwa [toReal_zero] at this
  have hlt : toReal (sqrtUp k (subUp one (nsmulDown 4 m))) < 1 := by
    have := subDown_le_sub (one : 𝕋) (sqrtUp k (subUp one (nsmulDown 4 m)))
    rw [toReal_one] at this
    linarith
  -- so `atanhUp` applies
  have hA := le_atanhUp 64 k (sqrtUp k (subUp one (nsmulDown 4 m))) (by linarith) hpos
  have hB := Real.artanh_le_artanh (by linarith : -1 < √(1 - 4 * toReal m)) hlt hss
  have hC := add_le_addUp (atanhUp 64 k (sqrtUp k (subUp one (nsmulDown 4 m))))
    (atanhUp 64 k (sqrtUp k (subUp one (nsmulDown 4 m))))
  linarith

/-- The box around the stationary point `t₀` exists and holds it, where `t₀` is in `[l, u]`. -/
private theorem aux_stationaryBox (k : ℕ) (m l u : 𝕋) (hm : 0 < toReal m) (hm4 : toReal m ≤ 1 / 4)
    {b : ℝ} (hl : toReal l ≤ b) (hu : b ≤ toReal u)
    (hb : b = 2 * Real.artanh (√(1 - 4 * toReal m))) : -- --- CONCL ---
    ∃ a' b', step_stationaryBox k m l u = some (a', b') ∧ toReal a' ≤ b ∧
      b ≤ toReal b' := by -- --- PROOF ---
  have hlo : toReal (step_stationaryLo k m) ≤ b := hb ▸ aux_stationaryLo_le k m hm
  unfold step_stationaryBox
  dsimp only
  -- the ends in either order still hold the point, with or without an upper bound
  cases hH : step_stationaryHi k m with
  | none =>
    dsimp only
    -- no upper bound: the box runs to `u`
    refine ⟨maximum l (step_stationaryLo k m), u, ?_, ?_, hu⟩
    · rw [if_neg]
      intro h
      have := toReal_lt_of_ltStrict h
      rw [toReal_maximum] at this
      linarith [max_le hl hlo]
    · rw [toReal_maximum]; exact max_le hl hlo
  | some h =>
    -- the point is above `min` of the ends and below `max` of them, in either order
    have hhi : b ≤ toReal h := hb ▸ aux_le_stationaryHi k m h hm hm4 hH
    have hA : toReal (maximum l (minimum (step_stationaryLo k m) h)) ≤ b := by
      rw [toReal_maximum, toReal_minimum]; exact max_le hl (le_trans (min_le_left _ _) hlo)
    have hB : b ≤ toReal (minimum u (maximum (step_stationaryLo k m) h)) := by
      rw [toReal_minimum, toReal_maximum]; exact le_min hu (le_trans hhi (le_max_right _ _))
    dsimp only
    refine ⟨maximum l (minimum (step_stationaryLo k m) h),
      minimum u (maximum (step_stationaryLo k m) h), ?_, hA, hB⟩
    rw [if_neg]
    intro hc
    have := toReal_lt_of_ltStrict hc
    linarith

/-- A point of the box where `σ' = m` is in one of the candidate boxes. -/
private theorem aux_candidates_cover (k : ℕ) (m l u : 𝕋) {b : ℝ} (hl : toReal l ≤ b)
    (hu : b ≤ toReal u) (hd : Real.sigmoidDeriv b = toReal m) : -- --- CONCL ---
    ∃ c ∈ step_candidates k m l u, toReal c.1 ≤ b ∧ b ≤ toReal c.2 := by -- --- PROOF ---
  obtain ⟨hm, hm4, hcrit⟩ := Real.eq_pm_artanh_of_sigmoidDeriv hd
  unfold step_candidates
  rw [if_neg]
  · -- the point is `t₀` or `-t₀`, and its box is that of `t₀` or the reflected one
    rcases hcrit with h | h
    · obtain ⟨a', b', hs, ha, hb⟩ := aux_stationaryBox k m l u hm hm4 hl hu h
      exact ⟨(a', b'), by simp [hs], ha, hb⟩
    · obtain ⟨a', b', hs, ha, hb⟩ := aux_stationaryBox k m (neg u) (neg l) hm hm4
        (b := -b) (by rw [toReal_neg]; linarith) (by rw [toReal_neg]; linarith) (by linarith)
      refine ⟨(neg b', neg a'), by simp [hs], ?_, ?_⟩
      · simp only [toReal_neg]; linarith
      · simp only [toReal_neg]; linarith
  · -- `m ≤ 0` or `m > 1/4` is certified, which no `σ'` value is
    intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · have := toReal_le_of_le h
      rw [toReal_zero] at this
      linarith
    · have h1 := toReal_lt_of_ltStrict h
      have h2 := nsmulDown_le 4 m
      rw [toReal_one] at h1
      push_cast at h2
      linarith

/-- A fold of `maximum` over the candidates bounds whatever one candidate bounds. -/
private theorem aux_le_foldl_max {α : Type} (f : α → 𝕋) (x : ℝ) :
    ∀ (L : List α) (init : 𝕋), (x ≤ toReal init ∨ ∃ c ∈ L, x ≤ toReal (f c)) →
      x ≤ toReal (L.foldl (fun g c => maximum g (f c)) init)
  | [], init, h => by
    rcases h with h | ⟨c, hc, _⟩
    · exact h
    · simp at hc
  | c :: L, init, h => by
    refine aux_le_foldl_max f x L _ ?_
    rcases h with h | ⟨d, hd, hx⟩
    · exact Or.inl (by rw [toReal_maximum]; exact le_trans h (le_max_left _ _))
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact Or.inl (by rw [toReal_maximum]; exact le_trans hx (le_max_right _ _))
      · exact Or.inr ⟨d, hd, hx⟩

/-- The dual: a fold of `minimum` is under whatever one candidate is under. -/
private theorem aux_foldl_min_le {α : Type} (f : α → 𝕋) (x : ℝ) :
    ∀ (L : List α) (init : 𝕋), (toReal init ≤ x ∨ ∃ c ∈ L, toReal (f c) ≤ x) →
      toReal (L.foldl (fun g c => minimum g (f c)) init) ≤ x
  | [], init, h => by
    rcases h with h | ⟨c, hc, _⟩
    · exact h
    · simp at hc
  | c :: L, init, h => by
    refine aux_foldl_min_le f x L _ ?_
    rcases h with h | ⟨d, hd, hx⟩
    · exact Or.inl (by rw [toReal_minimum]; exact le_trans (min_le_left _ _) h)
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact Or.inl (by rw [toReal_minimum]; exact le_trans (min_le_right _ _) hx)
      · exact Or.inr ⟨d, hd, hx⟩

/-- The upper bound holds at every point of the box. -/
private theorem aux_extremumHi {E : Enclosure 𝕋} (hE : E.Encloses Real.sigmoid) (k : ℕ) (l u : 𝕋)
    {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
    Real.sigmoid t - toReal (regressionSlope E l u) * t ≤
      toReal (step_extremumHi E k l u) := by -- --- PROOF ---
  obtain ⟨⟨_, _, _, _⟩, ⟨q, hq, hmax, hcrit⟩⟩ := Real.exists_critical_extreme Real.sigmoid
    Real.sigmoidDeriv (toReal (regressionSlope E l u)) (toReal l) (toReal u)
    Real.hasDerivAt_sigmoid (le_trans hl hu)
  refine le_trans (hmax t ⟨hl, hu⟩) ?_
  unfold step_extremumHi
  refine aux_le_foldl_max _ _ _ _ ?_
  rcases hcrit with h | h | h
  · exact Or.inl (by
      rw [toReal_maximum]
      exact le_trans (aux_extremumUp hE _ _ _ h.symm.le h.le) (le_max_left _ _))
  · exact Or.inl (by
      rw [toReal_maximum]
      exact le_trans (aux_extremumUp hE _ _ _ h.symm.le h.le) (le_max_right _ _))
  · obtain ⟨c, hc, h1, h2⟩ := aux_candidates_cover k _ l u hq.1 hq.2 h
    exact Or.inr ⟨c, hc, aux_extremumUp hE _ _ _ h1 h2⟩

/-- The lower bound holds at every point of the box. -/
private theorem aux_extremumMin {E : Enclosure 𝕋} (hE : E.Encloses Real.sigmoid) (k : ℕ) (l u : 𝕋)
    {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
    toReal (step_extremumMin E k l u) ≤
      Real.sigmoid t - toReal (regressionSlope E l u) * t := by -- --- PROOF ---
  obtain ⟨⟨q, hq, hmin, hcrit⟩, _⟩ := Real.exists_critical_extreme Real.sigmoid
    Real.sigmoidDeriv (toReal (regressionSlope E l u)) (toReal l) (toReal u)
    Real.hasDerivAt_sigmoid (le_trans hl hu)
  refine le_trans ?_ (hmin t ⟨hl, hu⟩)
  unfold step_extremumMin
  refine aux_foldl_min_le _ _ _ _ ?_
  rcases hcrit with h | h | h
  · exact Or.inl (by
      rw [toReal_minimum]
      exact le_trans (min_le_left _ _) (aux_extremumLo hE _ _ _ h.symm.le h.le))
  · exact Or.inl (by
      rw [toReal_minimum]
      exact le_trans (min_le_right _ _) (aux_extremumLo hE _ _ _ h.symm.le h.le))
  · obtain ⟨c, hc, h1, h2⟩ := aux_candidates_cover k _ l u hq.1 hq.2 h
    exact Or.inr ⟨c, hc, aux_extremumLo hE _ _ _ h1 h2⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidRegressionExactRelaxation_encloses (k : ℕ) : -- --- CONCL ---
    (sigmoidRegressionExactRelaxation (𝕋 := 𝕋) k).Encloses Real.sigmoid := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  -- the bounds of `σ t - m t` over the box, and the names of what the relaxation stores
  have hH := aux_extremumHi (sigmoidEnclosure_encloses (𝕋 := 𝕋) k) k l u hl hu
  have hM := aux_extremumMin (sigmoidEnclosure_encloses (𝕋 := 𝕋) k) k l u hl hu
  set E := sigmoidEnclosure (𝕋 := 𝕋) k
  set c := step_extremumMid E k l u
  -- the error is at least the distance from the offset to either bound
  have e1 := sub_le_subUp (step_extremumHi E k l u) c
  have e2 := sub_le_subUp c (step_extremumMin E k l u)
  have e3 := le_max_left (toReal (subUp (step_extremumHi E k l u) c))
    (toReal (subUp c (step_extremumMin E k l u)))
  have e4 := le_max_right (toReal (subUp (step_extremumHi E k l u) c))
    (toReal (subUp c (step_extremumMin E k l u)))
  show |Real.sigmoid t - (toReal (regressionSlope E l u) * t + toReal c)| ≤ toReal (maximum _ _)
  rw [toReal_maximum, abs_le]
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
