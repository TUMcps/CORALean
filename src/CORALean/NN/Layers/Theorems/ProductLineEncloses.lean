module

public import CORALean.NN.Layers.Operations.ProductLine
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The line of a product on a zonotope is sound

For `a = c_a + x`, `b = c_b + y`, `a b - (c_b a + c_a b) = x y - c_a c_b`. At a scale `k > 0`,
`4 x y = (k x + y / k)² - (k x - y / k)²`; `|k x ± y / k|` is at most `∑ⱼ |k G_aⱼ ± G_bⱼ / k|
|βⱼ| + k |r_a| + |r_b| / k`, below the stored `S(k)` and `D(k)`, each term the larger magnitude
of its two roundings. So `x y` lies in `[-D(k)² / 4, S(k)² / 4]` at `k = 1` and at the stored
`λ ≥ τ > 0`, and in the tighter of the two. The offset is below the middle minus `c_a c_b` and
its upper rounding above it; the error pays half the width and that gap, and the margin is not
negative.

## Inputs
* `p` – the square root's Newton steps
* `τ` – the least scale
* `w₁` – the margin's factor of the larger end
* `w₂` – the margin's factor of the centers' product
* `ca` – center of `a`
* `cb` – center of `b`
* `Ga` – generators of `a`
* `Gb` – generators of `b`
* `ra` – radius of `a`'s interval center
* `rb` – radius of `b`'s interval center
* `β` – the factors, in `[-1, 1]`
* `sa` – the point of `a`'s interval center
* `sb` – the point of `b`'s interval center

## Hypotheses
* `hτ` – the least scale is positive
* `hw₁` – the first factor is not negative
* `hw₂` – the second factor is not negative
* `hβ` – the factors lie in `[-1, 1]`
* `hsa` – `a`'s interval point is within its radius
* `hsb` – `b`'s interval point is within its radius

## Conclusion
* `a b` is within the error of `c_b a + c_a b + offset`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A value between two floats is at most the larger of their magnitudes. -/
private theorem aux_abs_le_max {t : ℝ} {lo hi : 𝕋} (h1 : toReal lo ≤ t) (h2 : t ≤ toReal hi) :
    |t| ≤ toReal (maximum (absolute hi) (absolute lo)) := by
  rw [toReal_maximum, toReal_absolute, toReal_absolute, abs_le]
  constructor
  · have := neg_abs_le (toReal lo); have := le_max_right |toReal hi| |toReal lo|; linarith
  · have := le_abs_self (toReal hi); have := le_max_left |toReal hi| |toReal lo|; linarith

/-- The real span: `|∑ⱼ gⱼ βⱼ + k sa ± sb / k|` is at most `∑ⱼ Tⱼ + R` for `Tⱼ ≥ |gⱼ|`,
`R ≥ k ρ_a + ρ_b / k`. -/
private theorem aux_span {k ρa ρb sa sb R : ℝ} {g T β : Fin q → ℝ} (hk : 0 < k)
    (hβ : ∀ j, |β j| ≤ 1) (hT : ∀ j, |g j| ≤ T j) (hsa : |sa| ≤ ρa) (hsb : |sb| ≤ ρb)
    (hR : k * ρa + ρb / k ≤ R) (sgn : ℝ) (hsgn : |sgn| = 1) : -- --- CONCL ---
    |∑ j, g j * β j + (k * sa + sgn * (sb / k))| ≤ ∑ j, T j + R := by -- --- PROOF ---
  have hsum : |∑ j, g j * β j| ≤ ∑ j, T j := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) (hT j)
  have hrest : |k * sa + sgn * (sb / k)| ≤ k * ρa + ρb / k := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos hk]; exact mul_le_mul_of_nonneg_left hsa hk.le
    · rw [abs_mul, hsgn, one_mul, abs_div, abs_of_pos hk]
      exact div_le_div_of_nonneg_right hsb hk.le
  exact le_trans (abs_add_le _ _) (by linarith)

/-- The stored spans bound the real ones at a positive stored scale `k`. -/
private theorem aux_spans {k : 𝕋} (hk : 0 < toReal k) (Ga Gb : Fin q → 𝕋) {ra rb : 𝕋}
    {β : Fin q → ℝ} (hβ : ∀ j, |β j| ≤ 1) {sa sb : ℝ} (hsa : |sa| ≤ toReal ra)
    (hsb : |sb| ≤ toReal rb) : -- --- CONCL ---
    let x := ∑ j, toReal (Ga j) * β j + sa
    let y := ∑ j, toReal (Gb j) * β j + sb
    |toReal k * x + y / toReal k| ≤ toReal (step_productSumSpan k Ga Gb ra rb) ∧
      |toReal k * x - y / toReal k|
        ≤ toReal (step_productDiffSpan k Ga Gb ra rb) := by -- --- PROOF ---
  intro x y
  have hρb : 0 ≤ toReal rb := le_trans (abs_nonneg _) hsb
  have hρa : 0 ≤ toReal ra := le_trans (abs_nonneg _) hsa
  -- the rest `k ρ_a + ρ_b / k`
  have hinv := div_le_divUp one k hk
  rw [toReal_one] at hinv
  have hR : toReal k * toReal ra + toReal rb / toReal k
      ≤ toReal (addUp (mulUp ra k) (mulUp rb (divUp one k))) := by
    have h1 := mul_le_mulUp ra k
    have h2 := mul_le_mulUp rb (divUp one k)
    have h3 := add_le_addUp (mulUp ra k) (mulUp rb (divUp one k))
    have h4 : toReal rb / toReal k ≤ toReal rb * toReal (divUp one k) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hρb
    nlinarith
  -- the generator terms, each between its two roundings
  have hterm : ∀ (sgn : ℝ) (j : Fin q) (up dn : 𝕋),
      toReal dn ≤ toReal (Ga j) * toReal k + sgn * (toReal (Gb j) / toReal k) →
      toReal (Ga j) * toReal k + sgn * (toReal (Gb j) / toReal k) ≤ toReal up →
      |toReal k * toReal (Ga j) + sgn * (toReal (Gb j) / toReal k)|
        ≤ toReal (maximum (absolute up) (absolute dn)) := by
    intro sgn j up dn h1 h2
    rw [mul_comm (toReal k)]
    exact aux_abs_le_max h1 h2
  -- `k x ± y / k` as one sum over the factors plus the rests
  have hxy : ∀ sgn : ℝ, toReal k * x + sgn * (y / toReal k)
      = ∑ j, (toReal k * toReal (Ga j) + sgn * (toReal (Gb j) / toReal k)) * β j
        + (toReal k * sa + sgn * (sb / toReal k)) := by
    intro sgn
    have e1 : ∑ j, (toReal k * toReal (Ga j) + sgn * (toReal (Gb j) / toReal k)) * β j
        = toReal k * ∑ j, toReal (Ga j) * β j + sgn / toReal k * ∑ j, toReal (Gb j) * β j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]
    simp only [x, y]
    ring
  -- the sum's span, then the difference's
  constructor
  · unfold step_productSumSpan
    dsimp only
    have hS := sum_le_sumUp fun j => maximum (absolute (addUp (mulUp (Ga j) k) (divUp (Gb j) k)))
      (absolute (addDown (mulDown (Ga j) k) (divDown (Gb j) k)))
    have hS2 := add_le_addUp (sumUp fun j => maximum
      (absolute (addUp (mulUp (Ga j) k) (divUp (Gb j) k)))
      (absolute (addDown (mulDown (Ga j) k) (divDown (Gb j) k))))
      (addUp (mulUp ra k) (mulUp rb (divUp one k)))
    have := hxy 1
    rw [one_mul] at this
    rw [this]
    -- each term at the larger magnitude of its two roundings
    have hT : ∀ j, |toReal k * toReal (Ga j) + 1 * (toReal (Gb j) / toReal k)|
        ≤ toReal (maximum (absolute (addUp (mulUp (Ga j) k) (divUp (Gb j) k)))
          (absolute (addDown (mulDown (Ga j) k) (divDown (Gb j) k)))) := by
      intro j
      refine hterm 1 j _ _ ?_ ?_
      · have := addDown_le_add (mulDown (Ga j) k) (divDown (Gb j) k)
        have := mulDown_le_mul (Ga j) k
        have := divDown_le_div (Gb j) k hk
        linarith
      · have := add_le_addUp (mulUp (Ga j) k) (divUp (Gb j) k)
        have := mul_le_mulUp (Ga j) k
        have := div_le_divUp (Gb j) k hk
        linarith
    refine le_trans (aux_span hk hβ hT hsa hsb hR 1 (by simp)) ?_
    linarith
  · -- the difference: the same with `-1`
    unfold step_productDiffSpan
    dsimp only
    have hS := sum_le_sumUp fun j => maximum (absolute (subUp (mulUp (Ga j) k) (divDown (Gb j) k)))
      (absolute (subDown (mulDown (Ga j) k) (divUp (Gb j) k)))
    have hS2 := add_le_addUp (sumUp fun j => maximum
      (absolute (subUp (mulUp (Ga j) k) (divDown (Gb j) k)))
      (absolute (subDown (mulDown (Ga j) k) (divUp (Gb j) k))))
      (addUp (mulUp ra k) (mulUp rb (divUp one k)))
    have := hxy (-1)
    rw [neg_one_mul, ← sub_eq_add_neg] at this
    rw [this]
    -- each term at the larger magnitude of its two roundings
    have hT : ∀ j, |toReal k * toReal (Ga j) + -1 * (toReal (Gb j) / toReal k)|
        ≤ toReal (maximum (absolute (subUp (mulUp (Ga j) k) (divDown (Gb j) k)))
          (absolute (subDown (mulDown (Ga j) k) (divUp (Gb j) k)))) := by
      intro j
      refine hterm (-1) j _ _ ?_ ?_
      · have := subDown_le_sub (mulDown (Ga j) k) (divUp (Gb j) k)
        have := mulDown_le_mul (Ga j) k
        have := div_le_divUp (Gb j) k hk
        linarith
      · have := sub_le_subUp (mulUp (Ga j) k) (divDown (Gb j) k)
        have := mul_le_mulUp (Ga j) k
        have := divDown_le_div (Gb j) k hk
        linarith
    refine le_trans (aux_span hk hβ hT hsa hsb hR (-1) (by simp)) ?_
    linarith

/-- The real band of `x y` at a scale: between `-D² / 4` and `S² / 4` for `|k x ± y / k|` below
`S` and `D`. -/
private theorem aux_band {k x y S D : ℝ} (hk : 0 < k) (hS : |k * x + y / k| ≤ S)
    (hD : |k * x - y / k| ≤ D) : -- --- CONCL ---
    -(D * D) / 4 ≤ x * y ∧ x * y ≤ S * S / 4 := by -- --- PROOF ---
  have hid : 4 * (x * y) = (k * x + y / k) ^ 2 - (k * x - y / k) ^ 2 := by
    field_simp; ring
  have h1 : (k * x + y / k) ^ 2 ≤ S * S := by
    rw [← sq_abs, pow_two]; exact mul_self_le_mul_self (abs_nonneg _) hS
  have h2 : (k * x - y / k) ^ 2 ≤ D * D := by
    rw [← sq_abs, pow_two]; exact mul_self_le_mul_self (abs_nonneg _) hD
  constructor <;> nlinarith [sq_nonneg (k * x + y / k), sq_nonneg (k * x - y / k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem productLine_encloses (p : ℕ) {τ w₁ w₂ : 𝕋} (hτ : 0 < toReal τ) (hw₁ : 0 ≤ toReal w₁)
    (hw₂ : 0 ≤ toReal w₂) (ca cb : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) {β : Fin q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) {sa sb : ℝ} (hsa : |sa| ≤ toReal ra)
    (hsb : |sb| ≤ toReal rb) : -- --- CONCL ---
    let a := toReal ca + (∑ j, toReal (Ga j) * β j + sa)
    let b := toReal cb + (∑ j, toReal (Gb j) * β j + sb)
    |a * b - (toReal cb * a + toReal ca * b + toReal (productLine p τ w₁ w₂ ca cb Ga Gb ra rb).1)|
      ≤ toReal (productLine p τ w₁ w₂ ca cb Ga Gb ra rb).2 := by -- --- PROOF ---
  intro a b
  simp only [productLine]
  set x := ∑ j, toReal (Ga j) * β j + sa with hx
  set y := ∑ j, toReal (Gb j) * β j + sb with hy
  -- the band of `x y` at both scales, read through the stored ends
  set lam := step_productScale p τ Ga Gb ra rb with hlam
  have hlam0 : 0 < toReal lam := by
    rw [hlam, step_productScale]
    rw [toReal_maximum]; exact lt_of_lt_of_le hτ (le_max_right _ _)
  have hone : (0 : ℝ) < toReal (one : 𝕋) := by rw [toReal_one]; exact one_pos
  obtain ⟨hS1, hD1⟩ := aux_spans hone Ga Gb hβ hsa hsb
  obtain ⟨hS2, hD2⟩ := aux_spans hlam0 Ga Gb hβ hsa hsb
  have hb1 := aux_band hone hS1 hD1
  have hb2 := aux_band hlam0 hS2 hD2
  set lo := step_productLo p τ Ga Gb ra rb with hlo
  set hi := step_productHi p τ Ga Gb ra rb with hhi
  have hloR : toReal lo ≤ x * y := by
    rw [hlo, step_productLo, ← hlam]
    rw [toReal_maximum, toReal_neg, toReal_neg, toReal_half, toReal_half, toReal_half, toReal_half]
    have h1 := mul_le_mulUp (step_productDiffSpan one Ga Gb ra rb)
      (step_productDiffSpan one Ga Gb ra rb)
    have h2 := mul_le_mulUp (step_productDiffSpan lam Ga Gb ra rb)
      (step_productDiffSpan lam Ga Gb ra rb)
    exact max_le (by linarith [hb1.1]) (by linarith [hb2.1])
  -- the upper end, the smaller of the two scales' squares
  have hhiR : x * y ≤ toReal hi := by
    rw [hhi, step_productHi, ← hlam]
    rw [toReal_minimum, toReal_half, toReal_half, toReal_half, toReal_half]
    have h1 := mul_le_mulUp (step_productSumSpan one Ga Gb ra rb)
      (step_productSumSpan one Ga Gb ra rb)
    have h2 := mul_le_mulUp (step_productSumSpan lam Ga Gb ra rb)
      (step_productSumSpan lam Ga Gb ra rb)
    exact le_min (by linarith [hb1.2]) (by linarith [hb2.2])
  -- the line leaves `x y - c_a c_b`
  have hleft : a * b - (toReal cb * a + toReal ca * b) = x * y - toReal ca * toReal cb := by
    simp only [a, b, ← hx, ← hy]; ring
  -- the offset, its upper rounding and the margin
  have hcU := mul_le_mulUp ca cb
  have hcD := mulDown_le_mul ca cb
  have hsD := addDown_le_add lo hi
  have hsU := add_le_addUp lo hi
  have hoD := subDown_le_sub (half (addDown lo hi)) (mulUp ca cb)
  have hoU := sub_le_subUp (half (addUp lo hi)) (mulDown ca cb)
  have hgap := sub_le_subUp (subUp (half (addUp lo hi)) (mulDown ca cb))
    (subDown (half (addDown lo hi)) (mulUp ca cb))
  have hw := sub_le_subUp hi lo
  rw [toReal_half] at hoD hoU
  -- the margin is not negative: the upper end is a square
  have hhi0 : 0 ≤ toReal hi := by
    rw [hhi, step_productHi, ← hlam]
    rw [toReal_minimum, toReal_half, toReal_half, toReal_half, toReal_half]
    have h1 := mul_le_mulUp (step_productSumSpan one Ga Gb ra rb)
      (step_productSumSpan one Ga Gb ra rb)
    have h2 := mul_le_mulUp (step_productSumSpan lam Ga Gb ra rb)
      (step_productSumSpan lam Ga Gb ra rb)
    exact le_min (by linarith [mul_self_nonneg (toReal (step_productSumSpan one Ga Gb ra rb))])
      (by linarith [mul_self_nonneg (toReal (step_productSumSpan lam Ga Gb ra rb))])
  have hbig : 0 ≤ toReal (maximum hi (neg lo)) := by
    rw [toReal_maximum]; exact le_trans hhi0 (le_max_left _ _)
  have hm1 := mul_le_mulUp (maximum hi (neg lo)) w₁
  have hm2 := mul_le_mulUp (absolute (mulUp ca cb)) w₂
  have habs : 0 ≤ toReal (absolute (mulUp ca cb)) := by rw [toReal_absolute]; exact abs_nonneg _
  have hm3 := add_le_addUp (mulUp (maximum hi (neg lo)) w₁) (mulUp (absolute (mulUp ca cb)) w₂)
  have hwiden : 0 ≤ toReal (addUp (mulUp (maximum hi (neg lo)) w₁)
      (mulUp (absolute (mulUp ca cb)) w₂)) := by
    linarith [mul_nonneg hbig hw₁, mul_nonneg habs hw₂]
  -- the error at least half the width, the gap and the margin
  have he1 := add_le_addUp (half (subUp hi lo))
    (subUp (subUp (half (addUp lo hi)) (mulDown ca cb)) (subDown (half (addDown lo hi))
      (mulUp ca cb)))
  have he2 := add_le_addUp (addUp (half (subUp hi lo))
    (subUp (subUp (half (addUp lo hi)) (mulDown ca cb)) (subDown (half (addDown lo hi))
      (mulUp ca cb)))) (addUp (mulUp (maximum hi (neg lo)) w₁) (mulUp (absolute (mulUp ca cb)) w₂))
  rw [toReal_half] at he1
  rw [show a * b - (toReal cb * a + toReal ca * b
      + toReal (subDown (half (addDown lo hi)) (mulUp ca cb)))
    = x * y - toReal ca * toReal cb - toReal (subDown (half (addDown lo hi)) (mulUp ca cb)) by
      linarith [hleft]]
  rw [abs_le]
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
