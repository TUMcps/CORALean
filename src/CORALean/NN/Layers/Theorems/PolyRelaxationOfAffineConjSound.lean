import CORALean.NN.Layers.Operations.PolyRelaxationOfAffineConj
import CORALean.NN.Layers.Theorems.LeEvalPolyUp
import CORALean.NN.Layers.Theorems.OfAffineConjSound
import CORALean.NN.Layers.Theorems.Real.EvalPolyScaleCoeffs
import CORALean.NN.Layers.Theorems.Real.EvalPolyShiftConst

/-!
# A polynomial relaxation carried along an affine conjugation is sound

`g t = ra f (rb t) + c` inherits `f`'s polynomial soundness: against the exactly rescaled
polynomial the deviation is `ra` times `f`'s, and the stored coefficients, each rounded up from
an exact one that the two roundings bracket, move the polynomial by at most the evaluation of
the gaps at `max(|l|, |u|)`. The two scales arrive here as hypotheses on the roundings.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ} {ra rb : ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_pow_iterate_up_le {B : ScaleRounding 𝕋} (hB : B.Sound rb) (hb : 0 < rb) (x : 𝕋)
    (k : ℕ) : rb ^ k * toReal x ≤ toReal (B.up^[k] x) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have h1 := hB.up_ge (B.up^[k] x)
    have h2 := mul_le_mul_of_nonneg_left ih hb.le
    nlinarith

theorem aux_iterate_down_le_pow {B : ScaleRounding 𝕋} (hB : B.Sound rb) (hb : 0 < rb) (x : 𝕋)
    (k : ℕ) : toReal (B.down^[k] x) ≤ rb ^ k * toReal x := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have h1 := hB.down_le (B.down^[k] x)
    have h2 := mul_le_mul_of_nonneg_left ih hb.le
    nlinarith

theorem aux_abs_le_tBound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |t| ≤ toReal (Relaxation.conjTBound l u) := by -- --- PROOF ---
  rw [Relaxation.conjTBound, toReal_maximum, toReal_absolute, toReal_absolute, abs_le]
  have hnl : -toReal l ≤ |toReal l| := by rw [← abs_neg]; exact le_abs_self _
  have hnu : toReal u ≤ |toReal u| := le_abs_self _
  have := le_max_left |toReal l| |toReal u|
  have := le_max_right |toReal l| |toReal u|
  exact ⟨by linarith, by linarith⟩

/-- The exact conjugated coefficients lie between the two roundings. -/
theorem aux_conjCoeffs_bracket {A B : ScaleRounding 𝕋} (hA : A.Sound ra) (hB : B.Sound rb)
    (ha : 0 < ra) (hb : 0 < rb) (c : 𝕋) (p : Fin (m + 1) → 𝕋) (i : Fin (m + 1)) :
    toReal (conjCoeffsDown A B c p i)
        ≤ Real.shiftConst (Real.scaleCoeffs (fun k => toReal (p k)) ra rb) (toReal c) i
      ∧ Real.shiftConst (Real.scaleCoeffs (fun k => toReal (p k)) ra rb) (toReal c) i
        ≤ toReal (conjCoeffsUp A B c p i) := by -- --- PROOF ---
  have h1 := aux_pow_iterate_up_le hB hb (p i) i
  have h2 := hA.up_ge (B.up^[(i : ℕ)] (p i))
  have h3 := mul_le_mul_of_nonneg_left h1 ha.le
  have g1 := aux_iterate_down_le_pow hB hb (p i) i
  have g2 := hA.down_le (B.down^[(i : ℕ)] (p i))
  have g3 := mul_le_mul_of_nonneg_left g1 ha.le
  by_cases h : i = 0
  · have u := add_le_addUp (A.up (B.up^[(i : ℕ)] (p i))) c
    have d := addDown_le_add (A.down (B.down^[(i : ℕ)] (p i))) c
    simp only [conjCoeffsUp, conjCoeffsDown, Real.shiftConst, Real.scaleCoeffs, if_pos h]
    constructor <;> nlinarith
  · simp only [conjCoeffsUp, conjCoeffsDown, Real.shiftConst, Real.scaleCoeffs, if_neg h,
      add_zero]
    constructor <;> nlinarith

/-- What rounding the coefficients can move the polynomial by, over the box. -/
theorem aux_evalPoly_conjCoeffs_le {A B : ScaleRounding 𝕋} (hA : A.Sound ra) (hB : B.Sound rb)
    (ha : 0 < ra) (hb : 0 < rb) (c : 𝕋) (p : Fin (m + 1) → 𝕋) {t : ℝ} {T : 𝕋}
    (hT : |t| ≤ toReal T) :
    |Real.evalPoly (fun k => toReal (conjCoeffsUp A B c p k)) t
        - (ra * Real.evalPoly (fun k => toReal (p k)) (rb * t) + toReal c)|
      ≤ toReal (evalPolyUp (conjCoeffsGap A B c p) T) := by -- --- PROOF ---
  rw [show ra * Real.evalPoly (fun k => toReal (p k)) (rb * t) + toReal c
      = Real.evalPoly (Real.shiftConst (Real.scaleCoeffs (fun k => toReal (p k)) ra rb)
          (toReal c)) t by
    rw [Real.evalPoly_shiftConst, Real.evalPoly_scaleCoeffs]]
  have hgap : ∀ i, |toReal (conjCoeffsUp A B c p i)
      - Real.shiftConst (Real.scaleCoeffs (fun k => toReal (p k)) ra rb) (toReal c) i|
      ≤ toReal (conjCoeffsGap A B c p i) := by
    intro i
    obtain ⟨h1, h2⟩ := aux_conjCoeffs_bracket hA hB ha hb c p i
    have h3 := sub_le_subUp (conjCoeffsUp A B c p i) (conjCoeffsDown A B c p i)
    rw [abs_of_nonneg (by linarith)]
    show _ ≤ toReal (subUp _ _)
    linarith
  -- term by term: the gap times the box bound dominates the coefficient deviation times `t^i`
  refine le_trans ?_ (le_evalPolyUp (conjCoeffsGap A B c p) T)
  show |∑ i, toReal (conjCoeffsUp A B c p i) * t ^ (i : ℕ)
      - ∑ i, Real.shiftConst (Real.scaleCoeffs (fun k => toReal (p k)) ra rb) (toReal c) i
        * t ^ (i : ℕ)| ≤ ∑ i, toReal (conjCoeffsGap A B c p i) * toReal T ^ (i : ℕ)
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul, abs_pow]
  exact mul_le_mul (hgap i) (pow_le_pow_left₀ (abs_nonneg t) hT _) (by positivity)
    (le_trans (abs_nonneg _) (hgap i))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `g t = ra f (rb t) + c` inherits `f`'s polynomial soundness. -/
theorem PolyRelaxation.ofAffineConj_sound {P : PolyRelaxation 𝕋 m} {A B : ScaleRounding 𝕋}
    {c : 𝕋} {f g : ℝ → ℝ} (hP : P.Sound f) (hA : A.Sound ra) (hB : B.Sound rb) (ha : 0 < ra)
    (hb : 0 < rb) (hg : ∀ t, g t = ra * f (rb * t) + toReal c) :
    (PolyRelaxation.ofAffineConj P A B c).Sound g := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  -- the box maps to the box `rb` sends it to, where `P` is sound
  have hbl : toReal (B.down l) ≤ rb * t :=
    le_trans (hB.down_le l) (mul_le_mul_of_nonneg_left hl hb.le)
  have hbu : rb * t ≤ toReal (B.up u) :=
    le_trans (mul_le_mul_of_nonneg_left hu hb.le) (hB.up_ge u)
  have h1 := hP.sound hbl hbu
  have h2 := aux_evalPoly_conjCoeffs_le hA hB ha hb c (P.coeffs (B.down l) (B.up u))
    (aux_abs_le_tBound hl hu)
  have h3 := hA.up_ge (P.error (B.down l) (B.up u))
  have h4 := add_le_addUp (A.up (P.error (B.down l) (B.up u)))
    (evalPolyUp (conjCoeffsGap A B c (P.coeffs (B.down l) (B.up u)))
      (Relaxation.conjTBound l u))
  -- the conjugation's scaling is all that separates the two deviations
  have heq : g t - ra * Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t)
      - toReal c = ra * (f (rb * t)
        - Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t)) := by
    rw [hg t]; ring
  have h5 : |g t - (ra * Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k))
      (rb * t) + toReal c)| ≤ ra * toReal (P.error (B.down l) (B.up u)) := by
    rw [show g t - (ra * Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k))
      (rb * t) + toReal c) = ra * (f (rb * t)
        - Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t)) by
      rw [← heq]; ring, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left h1 ha.le
  -- split into the deviation from the exact conjugate and the coefficient roundings
  show |g t - Real.evalPoly (fun k => toReal (conjCoeffsUp A B c
      (P.coeffs (B.down l) (B.up u)) k)) t| ≤ toReal (addUp _ _)
  have h6 := abs_add_le (g t - (ra * Real.evalPoly
      (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t) + toReal c))
    ((ra * Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t)
      + toReal c) - Real.evalPoly (fun k => toReal (conjCoeffsUp A B c
        (P.coeffs (B.down l) (B.up u)) k)) t)
  rw [abs_sub_comm (ra * Real.evalPoly _ (rb * t) + toReal c)] at h6
  -- the triangle inequality, with the two pieces bounded above
  rw [show g t - Real.evalPoly (fun k => toReal (conjCoeffsUp A B c
        (P.coeffs (B.down l) (B.up u)) k)) t = (g t - (ra * Real.evalPoly
      (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t) + toReal c))
    + ((ra * Real.evalPoly (fun k => toReal (P.coeffs (B.down l) (B.up u) k)) (rb * t)
      + toReal c) - Real.evalPoly (fun k => toReal (conjCoeffsUp A B c
        (P.coeffs (B.down l) (B.up u)) k)) t) by ring]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
