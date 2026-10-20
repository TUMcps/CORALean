module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.SinCos
public import CORALean.Global.Float.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# `arctan`, `arcsin` and `arccos` rounded in either direction

All three are one bisection of an arctangent of a half angle: `arctan y = 2 arctan (y / (1 + √(1 +
y²)))`, `arcsin x = 2 arctan (x / (1 + √(1 - x²)))`, `arccos x = 2 arcsin √((1 - x)/2)`, the
half-angle formula `tan (t/2) = sin t / (1 + cos t)`. The inner argument `z` lies in `[-1, 1]`, so
`arctan z` is bisected there: a midpoint `m` has `cos m > 0`, so `m ≤ arctan z` is `sin m ≤ z cos
m`, which `sinUp`/`cosDown`/`cosUp` certify. A step certifying neither keeps the bracket, so the
result is sound for any fuel. `arcsin` and `arccos` clamp their argument to `[-1, 1]` first
(`Real.arcsin_projIcc`), so all six are total. `n` is the number of halvings of the sine and cosine,
`k` the number of bisection and Newton steps.

## Inputs
* `n` – number of halvings
* `k` – number of bisection steps
* `y` – float argument

## Hypotheses
* none

## Conclusion
* the downward arctangent is at most the arctangent
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

namespace InverseTrig

/-- Into `[-1, 1]`. -/
def clampOne (a : 𝕋) : 𝕋 := maximum (neg one) (minimum one a)

/-- One bisection step for `arctan z` in `b`, at a midpoint clamped into `[-1, 1]`. -/
def atanStep (n : ℕ) (z : 𝕋) (b : Interval 𝕋) : Interval 𝕋 :=
  let m := clampOne (half (addUp b.inf b.sup))
  let cl := cosDown n m
  let cu := cosUp n m
  if le (sinUp n m) (minimum (mulDown z cl) (mulDown z cu)) = true then ⟨m, b.sup⟩  -- tan m ≤ z
  else if le (maximum (mulUp z cl) (mulUp z cu)) (sinDown n m) = true then ⟨b.inf, m⟩ -- z ≤ tan m
  else b

def atanIter (n : ℕ) (z : 𝕋) : ℕ → Interval 𝕋 → Interval 𝕋
  | 0, b => b
  | j + 1, b => atanIter n z j (atanStep n z b)

/-- `arctan z` bracketed, `z` clamped into `[-1, 1]` first. -/
def atanBracket (n k : ℕ) (z : 𝕋) : Interval 𝕋 := atanIter n (clampOne z) k ⟨neg one, one⟩

/-- `num / D` from below and above, for `D` between `dl ≥ 1` and `du`. -/
def quotLo (num dl du : 𝕋) : 𝕋 := minimum (divDown num dl) (divDown num du)
def quotHi (num dl du : 𝕋) : 𝕋 := maximum (divUp num dl) (divUp num du)

/-- `1 + √(1 + y²)`, from below and above. -/
def atanDenLo (k : ℕ) (y : 𝕋) : 𝕋 :=
  maximum one (addDown one (sqrtDown k (addDown one (mulDown y y))))
def atanDenHi (k : ℕ) (y : 𝕋) : 𝕋 := addUp one (sqrtUp k (addUp one (mulUp y y)))

/-- `1 + √(1 - x²)`, from below and above. -/
def asinDenLo (k : ℕ) (x : 𝕋) : 𝕋 :=
  maximum one (addDown one (sqrtDown k (subDown one (mulUp x x))))
def asinDenHi (k : ℕ) (x : 𝕋) : 𝕋 := addUp one (sqrtUp k (subUp one (mulDown x x)))

end InverseTrig

open InverseTrig

/-- `arctan y` from below, at every `y`. -/
def atanDown (n k : ℕ) (y : 𝕋) : 𝕋 :=
  let z := quotLo y (atanDenLo k y) (atanDenHi k y)
  let b := atanBracket n k z
  addDown b.inf b.inf

/-- `arctan y` from above, at every `y`. -/
def atanUp (n k : ℕ) (y : 𝕋) : 𝕋 :=
  let z := quotHi y (atanDenLo k y) (atanDenHi k y)
  let b := atanBracket n k z
  addUp b.sup b.sup

/-- `arcsin x` from below, at every `x` (`Real.arcsin` is constant outside `[-1, 1]`). -/
def asinDown (n k : ℕ) (x : 𝕋) : 𝕋 :=
  let x' := clampOne x
  let z := quotLo x' (asinDenLo k x') (asinDenHi k x')
  let b := atanBracket n k z
  addDown b.inf b.inf

/-- `arcsin x` from above, at every `x`. -/
def asinUp (n k : ℕ) (x : 𝕋) : 𝕋 :=
  let x' := clampOne x
  let z := quotHi x' (asinDenLo k x') (asinDenHi k x')
  let b := atanBracket n k z
  addUp b.sup b.sup

/-- `arccos x` from below, at every `x`: twice `arcsin √((1 - x)/2)`. -/
def acosDown (n k : ℕ) (x : 𝕋) : 𝕋 :=
  let x' := clampOne x
  let w := sqrtDown k (half (subDown one x'))
  let a := asinDown n k w
  addDown a a

/-- `arccos x` from above, at every `x`. -/
def acosUp (n k : ℕ) (x : 𝕋) : 𝕋 :=
  let x' := clampOne x
  let w := sqrtUp k (half (subUp one x'))
  let a := asinUp n k w
  addUp a a

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

private theorem toReal_clampOne (a : 𝕋) :
    toReal (clampOne a) = max (-1) (min 1 (toReal a)) := by
  rw [clampOne, toReal_maximum, toReal_minimum, toReal_neg, toReal_one]

private theorem abs_clampOne_le (a : 𝕋) : |toReal (clampOne a)| ≤ 1 := by
  rw [toReal_clampOne, abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Clamping a lower bound of a value in `[-1, 1]` keeps it a lower bound. -/
private theorem clampOne_le {a : 𝕋} {v : ℝ} (h : toReal a ≤ v) (hv : |v| ≤ 1) :
    toReal (clampOne a) ≤ v := by
  rw [toReal_clampOne]
  rw [abs_le] at hv
  exact max_le hv.1 (le_trans (min_le_right _ _) h)

private theorem le_clampOne {a : 𝕋} {v : ℝ} (h : v ≤ toReal a) (hv : |v| ≤ 1) :
    v ≤ toReal (clampOne a) := by
  rw [toReal_clampOne]
  rw [abs_le] at hv
  exact le_max_of_le_right (le_min hv.2 h)

/-- The half-angle formula, `tan (t/2) = sin t / (1 + cos t)`, as an arctangent. -/
private theorem arctan_half_angle {t : ℝ} (h1 : -Real.pi < t) (h2 : t < Real.pi) : -- --- CONCL ---
    Real.arctan (Real.sin t / (1 + Real.cos t)) = t / 2 := by -- --- PROOF ---
  have hc : 0 < Real.cos (t / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hcos : 1 + Real.cos t = 2 * Real.cos (t / 2) ^ 2 := by
    rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul]; ring_nf
  have heq : Real.sin t / (1 + Real.cos t) = Real.tan (t / 2) := by
    rw [hs, hcos, Real.tan_eq_sin_div_cos]
    field_simp
  rw [heq, Real.arctan_tan (by linarith) (by linarith)]

private theorem arctan_eq_two_mul (y : ℝ) : -- --- CONCL ---
    Real.arctan y = 2 * Real.arctan (y / (1 + Real.sqrt (1 + y ^ 2))) := by -- --- PROOF ---
  have hS : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h := arctan_half_angle (t := Real.arctan y)
    (by linarith [Real.neg_pi_div_two_lt_arctan y, Real.pi_pos])
    (by linarith [Real.arctan_lt_pi_div_two y, Real.pi_pos])
  rw [Real.sin_arctan, Real.cos_arctan] at h
  have heq : y / Real.sqrt (1 + y ^ 2) / (1 + 1 / Real.sqrt (1 + y ^ 2)) =
      y / (1 + Real.sqrt (1 + y ^ 2)) := by
    field_simp
    ring
  rw [heq] at h
  rw [h]; ring

private theorem arcsin_eq_two_mul {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : -- --- CONCL ---
    Real.arcsin x = 2 * Real.arctan (x / (1 + Real.sqrt (1 - x ^ 2))) := by -- --- PROOF ---
  have h := arctan_half_angle (t := Real.arcsin x)
    (by linarith [Real.neg_pi_div_two_le_arcsin x, Real.pi_pos])
    (by linarith [Real.arcsin_le_pi_div_two x, Real.pi_pos])
  rw [Real.sin_arcsin h1 h2, Real.cos_arcsin] at h
  rw [h]; ring

private theorem arccos_eq_two_mul {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : -- --- CONCL ---
    Real.arccos x = 2 * Real.arcsin (Real.sqrt ((1 - x) / 2)) := by -- --- PROOF ---
  set t := Real.arccos x
  have ht0 := Real.arccos_nonneg x
  have htp := Real.arccos_le_pi x
  have hcos : Real.cos t = x := Real.cos_arccos h1 h2
  have hs0 : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : Real.sin (t / 2) ^ 2 = (1 - x) / 2 := by
    have := Real.cos_sq_add_sin_sq (t / 2)
    have hc2 : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
      rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul]; ring_nf
    rw [← hcos]; linarith
  have hw : Real.sqrt ((1 - x) / 2) = Real.sin (t / 2) := by
    rw [← hsq, Real.sqrt_sq hs0]
  rw [hw, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
  ring

/-- `k x` lies between its values at the ends of `[c, d]`. -/
private theorem mul_between {k c d x : ℝ} (h1 : c ≤ x) (h2 : x ≤ d) : -- --- CONCL ---
    min (k * c) (k * d) ≤ k * x ∧ k * x ≤ max (k * c) (k * d) := by -- --- PROOF ---
  rcases le_total 0 k with hk | hk
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left h1 hk),
      le_max_of_le_right (mul_le_mul_of_nonneg_left h2 hk)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left h2 hk),
      le_max_of_le_left (mul_le_mul_of_nonpos_left h1 hk)⟩

/-- A bracket of `arctan z`. -/
private def Brackets (z : ℝ) (b : Interval 𝕋) : Prop :=
  toReal b.inf ≤ Real.arctan z ∧ Real.arctan z ≤ toReal b.sup

private theorem atanStep_brackets (n : ℕ) {z : 𝕋} {b : Interval 𝕋}
    (h : Brackets (toReal z) b) : -- --- CONCL ---
    Brackets (toReal z) (atanStep n z b) := by -- --- PROOF ---
  set m := clampOne (half (addUp b.inf b.sup))
  have hm := abs_clampOne_le (half (addUp b.inf b.sup))
  rw [abs_le] at hm
  have hpi := Real.pi_gt_three
  have hm1 : -(Real.pi / 2) < toReal m := by linarith [hm.1]
  have hm2 : toReal m < Real.pi / 2 := by linarith [hm.2]
  have hcos : 0 < Real.cos (toReal m) := Real.cos_pos_of_mem_Ioo ⟨hm1, hm2⟩
  have htan : Real.arctan (Real.sin (toReal m) / Real.cos (toReal m)) = toReal m := by
    rw [← Real.tan_eq_sin_div_cos, Real.arctan_tan hm1 hm2]
  have hzc := mul_between (k := toReal z) (cosDown_le n m) (le_cosUp n m)
  simp only [atanStep]
  split_ifs with h1 h2
  · -- `tan m ≤ z`, so `m ≤ arctan z`
    refine ⟨?_, h.2⟩
    have hle := toReal_le_of_le h1
    rw [toReal_minimum] at hle
    have hsz : Real.sin (toReal m) ≤ toReal z * Real.cos (toReal m) := by
      refine le_trans (le_sinUp n m) (le_trans hle ?_)
      exact le_trans (min_le_min (mulDown_le_mul _ _) (mulDown_le_mul _ _)) hzc.1
    rw [← htan]
    exact Real.arctan_strictMono.monotone ((div_le_iff₀ hcos).2 hsz)
  · -- `z ≤ tan m`, so `arctan z ≤ m`
    refine ⟨h.1, ?_⟩
    have hle := toReal_le_of_le h2
    rw [toReal_maximum] at hle
    have hsz : toReal z * Real.cos (toReal m) ≤ Real.sin (toReal m) := by
      refine le_trans (le_trans hzc.2 ?_) (le_trans hle (sinDown_le n m))
      exact max_le_max (mul_le_mulUp _ _) (mul_le_mulUp _ _)
    rw [← htan]
    exact Real.arctan_strictMono.monotone ((le_div_iff₀ hcos).2 hsz)
  · exact h

private theorem atanIter_brackets (n : ℕ) {z : 𝕋} :
    ∀ (j : ℕ) (b : Interval 𝕋), Brackets (toReal z) b → Brackets (toReal z) (atanIter n z j b) := by
  intro j
  induction j with
  | zero => exact fun _ h => h
  | succ j ih => exact fun b h => ih _ (atanStep_brackets n h)

/-- The bracket of the clamped argument holds `arctan` of it. -/
private theorem atanBracket_brackets (n k : ℕ) (z : 𝕋) : -- --- CONCL ---
    Brackets (toReal (clampOne z)) (atanBracket n k z) := by -- --- PROOF ---
  refine atanIter_brackets n k _ ?_
  have hz := abs_clampOne_le z
  have h4 := Real.pi_lt_four
  rw [abs_le] at hz
  have hlo : Real.arctan (-1) ≤ Real.arctan (toReal (clampOne z)) :=
    Real.arctan_strictMono.monotone hz.1
  have hhi : Real.arctan (toReal (clampOne z)) ≤ Real.arctan 1 :=
    Real.arctan_strictMono.monotone hz.2
  rw [Real.arctan_neg, Real.arctan_one] at hlo
  rw [Real.arctan_one] at hhi
  simp only [Brackets, toReal_neg, toReal_one]
  constructor <;> linarith

/-- `num / D` between the quotients by the two bounds on `D`. -/
private theorem quot_mem {num dl du : 𝕋} {D : ℝ} (hl1 : 1 ≤ toReal dl) (hl : toReal dl ≤ D)
    (hu : D ≤ toReal du) : -- --- CONCL ---
    toReal (quotLo num dl du) ≤ toReal num / D ∧
      toReal num / D ≤ toReal (quotHi num dl du) := by -- --- PROOF ---
  have hdl : 0 < toReal dl := by linarith
  have hD : 0 < D := by linarith
  have hdu : 0 < toReal du := by linarith
  have hb := mul_between (k := toReal num) (inv_anti₀ hD hu) (inv_anti₀ hdl hl)
  simp only [← div_eq_mul_inv] at hb
  simp only [quotLo, quotHi, toReal_minimum, toReal_maximum]
  constructor
  · refine le_trans ?_ hb.1
    rw [min_comm]
    exact min_le_min (divDown_le_div _ _ hdu) (divDown_le_div _ _ hdl)
  · refine le_trans hb.2 ?_
    rw [max_comm]
    exact max_le_max (div_le_divUp _ _ hdl) (div_le_divUp _ _ hdu)

private theorem atanDen_mem (k : ℕ) (y : 𝕋) : -- --- CONCL ---
    1 ≤ toReal (atanDenLo k y) ∧ toReal (atanDenLo k y) ≤ 1 + Real.sqrt (1 + toReal y ^ 2) ∧
      1 + Real.sqrt (1 + toReal y ^ 2) ≤ toReal (atanDenHi k y) := by -- --- PROOF ---
  have hr1 : toReal (addDown one (mulDown y y)) ≤ 1 + toReal y ^ 2 := by
    have h1 := addDown_le_add (one : 𝕋) (mulDown y y)
    have h2 := mulDown_le_mul y y
    rw [toReal_one] at h1; nlinarith
  have hr2 : 1 + toReal y ^ 2 ≤ toReal (addUp one (mulUp y y)) := by
    have h1 := add_le_addUp (one : 𝕋) (mulUp y y)
    have h2 := mul_le_mulUp y y
    rw [toReal_one] at h1; nlinarith
  have hs1 := le_trans (sqrtDown_le k _) (Real.sqrt_le_sqrt hr1)
  have hs2 := le_trans (Real.sqrt_le_sqrt hr2) (le_sqrtUp k _)
  refine ⟨?_, ?_, ?_⟩
  · rw [atanDenLo, toReal_maximum, toReal_one]; exact le_max_left _ _
  · rw [atanDenLo, toReal_maximum, toReal_one]
    refine max_le (by linarith [Real.sqrt_nonneg (1 + toReal y ^ 2)]) ?_
    have := addDown_le_add (one : 𝕋) (sqrtDown k (addDown one (mulDown y y)))
    rw [toReal_one] at this; linarith
  · have := add_le_addUp (one : 𝕋) (sqrtUp k (addUp one (mulUp y y)))
    rw [toReal_one] at this; rw [atanDenHi]; linarith

private theorem asinDen_mem (k : ℕ) (x : 𝕋) : -- --- CONCL ---
    1 ≤ toReal (asinDenLo k x) ∧ toReal (asinDenLo k x) ≤ 1 + Real.sqrt (1 - toReal x ^ 2) ∧
      1 + Real.sqrt (1 - toReal x ^ 2) ≤ toReal (asinDenHi k x) := by -- --- PROOF ---
  have hr1 : toReal (subDown one (mulUp x x)) ≤ 1 - toReal x ^ 2 := by
    have h1 := subDown_le_sub (one : 𝕋) (mulUp x x)
    have h2 := mul_le_mulUp x x
    rw [toReal_one] at h1; nlinarith
  have hr2 : 1 - toReal x ^ 2 ≤ toReal (subUp one (mulDown x x)) := by
    have h1 := sub_le_subUp (one : 𝕋) (mulDown x x)
    have h2 := mulDown_le_mul x x
    rw [toReal_one] at h1; nlinarith
  have hs1 := le_trans (sqrtDown_le k _) (Real.sqrt_le_sqrt hr1)
  have hs2 := le_trans (Real.sqrt_le_sqrt hr2) (le_sqrtUp k _)
  refine ⟨?_, ?_, ?_⟩
  · rw [asinDenLo, toReal_maximum, toReal_one]; exact le_max_left _ _
  · rw [asinDenLo, toReal_maximum, toReal_one]
    refine max_le (by linarith [Real.sqrt_nonneg (1 - toReal x ^ 2)]) ?_
    have := addDown_le_add (one : 𝕋) (sqrtDown k (subDown one (mulUp x x)))
    rw [toReal_one] at this; linarith
  · have := add_le_addUp (one : 𝕋) (sqrtUp k (subUp one (mulDown x x)))
    rw [toReal_one] at this; rw [asinDenHi]; linarith

/-- `|y / (1 + √·)| ≤ 1` for the two half-angle arguments. -/
private theorem abs_div_one_add_le {y s : ℝ} (hs : |y| ≤ 1 + s) (hs0 : 0 ≤ s) :
    |y / (1 + s)| ≤ 1 := by
  rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 1 + s)]
  exact div_le_one_of_le₀ hs (by linarith)

private theorem abs_le_one_add_sqrt_one_add (y : ℝ) : |y| ≤ 1 + Real.sqrt (1 + y ^ 2) := by
  have : |y| ≤ Real.sqrt (1 + y ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `arctan` at the lower end of the quotient, a lower bound by monotonicity. -/
private theorem twice_lower {z : 𝕋} {v : ℝ} (hz : toReal z ≤ v) (hv : |v| ≤ 1) (n k : ℕ) :
    toReal (addDown (atanBracket n k z).inf (atanBracket n k z).inf) ≤ 2 * Real.arctan v := by
  have hb := (atanBracket_brackets n k z).1
  have hm := Real.arctan_strictMono.monotone (clampOne_le hz hv)
  have := addDown_le_add (atanBracket n k z).inf (atanBracket n k z).inf
  linarith

/-- And at the upper end, an upper bound. -/
private theorem twice_upper {z : 𝕋} {v : ℝ} (hz : v ≤ toReal z) (hv : |v| ≤ 1) (n k : ℕ) :
    2 * Real.arctan v ≤ toReal (addUp (atanBracket n k z).sup (atanBracket n k z).sup) := by
  have hb := (atanBracket_brackets n k z).2
  have hm := Real.arctan_strictMono.monotone (le_clampOne hz hv)
  have := add_le_addUp (atanBracket n k z).sup (atanBracket n k z).sup
  linarith

/-- A clamped float is in `[-1, 1]`. -/
private theorem clampOne_mem (x : 𝕋) :
    -1 ≤ toReal (clampOne x) ∧ toReal (clampOne x) ≤ 1 := abs_le.1 (abs_clampOne_le x)

/-- Clamping does not move `Real.arcsin`. -/
private theorem arcsin_clampOne (x : 𝕋) :
    Real.arcsin (toReal (clampOne x)) = Real.arcsin (toReal x) := by
  rw [toReal_clampOne]
  have := Real.arcsin_projIcc (toReal x)
  rw [Set.coe_projIcc] at this
  rw [← this]

private theorem abs_le_one_add_sqrt_one_sub {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    |x| ≤ 1 + Real.sqrt (1 - x ^ 2) := by
  linarith [abs_le.2 ⟨h1, h2⟩, Real.sqrt_nonneg (1 - x ^ 2)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem atanDown_le (n k : ℕ) (y : 𝕋) : toReal (atanDown n k y) ≤ Real.arctan (toReal y) := by
  have hd := atanDen_mem k y
  rw [arctan_eq_two_mul]
  exact twice_lower (quot_mem hd.1 hd.2.1 hd.2.2).1
    (abs_div_one_add_le (abs_le_one_add_sqrt_one_add _) (Real.sqrt_nonneg _)) n k

theorem le_atanUp (n k : ℕ) (y : 𝕋) : Real.arctan (toReal y) ≤ toReal (atanUp n k y) := by
  have hd := atanDen_mem k y
  rw [arctan_eq_two_mul]
  exact twice_upper (quot_mem hd.1 hd.2.1 hd.2.2).2
    (abs_div_one_add_le (abs_le_one_add_sqrt_one_add _) (Real.sqrt_nonneg _)) n k

theorem asinDown_le (n k : ℕ) (x : 𝕋) : -- --- CONCL ---
    toReal (asinDown n k x) ≤ Real.arcsin (toReal x) := by -- --- PROOF ---
  have hc := clampOne_mem x
  have hd := asinDen_mem k (clampOne x)
  rw [← arcsin_clampOne, arcsin_eq_two_mul hc.1 hc.2]
  exact twice_lower (quot_mem hd.1 hd.2.1 hd.2.2).1
    (abs_div_one_add_le (abs_le_one_add_sqrt_one_sub hc.1 hc.2) (Real.sqrt_nonneg _)) n k

theorem le_asinUp (n k : ℕ) (x : 𝕋) : -- --- CONCL ---
    Real.arcsin (toReal x) ≤ toReal (asinUp n k x) := by -- --- PROOF ---
  have hc := clampOne_mem x
  have hd := asinDen_mem k (clampOne x)
  rw [← arcsin_clampOne, arcsin_eq_two_mul hc.1 hc.2]
  exact twice_upper (quot_mem hd.1 hd.2.1 hd.2.2).2
    (abs_div_one_add_le (abs_le_one_add_sqrt_one_sub hc.1 hc.2) (Real.sqrt_nonneg _)) n k

theorem acosDown_le (n k : ℕ) (x : 𝕋) : -- --- CONCL ---
    toReal (acosDown n k x) ≤ Real.arccos (toReal x) := by -- --- PROOF ---
  have hc := clampOne_mem x
  have hac : Real.arccos (toReal x) = Real.arccos (toReal (clampOne x)) := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin,
      arcsin_clampOne]
  rw [hac, arccos_eq_two_mul hc.1 hc.2]
  have hw : toReal (half (subDown one (clampOne x))) ≤ (1 - toReal (clampOne x)) / 2 := by
    have := subDown_le_sub (one : 𝕋) (clampOne x)
    rw [toReal_one] at this; rw [toReal_half]; linarith
  have hs := le_trans (sqrtDown_le k _) (Real.sqrt_le_sqrt hw)
  have ha := le_trans (asinDown_le n k _) (Real.arcsin_le_arcsin hs)
  have := addDown_le_add (asinDown n k (sqrtDown k (half (subDown one (clampOne x)))))
    (asinDown n k (sqrtDown k (half (subDown one (clampOne x)))))
  simp only [acosDown]
  linarith

theorem le_acosUp (n k : ℕ) (x : 𝕋) : -- --- CONCL ---
    Real.arccos (toReal x) ≤ toReal (acosUp n k x) := by -- --- PROOF ---
  have hc := clampOne_mem x
  have hac : Real.arccos (toReal x) = Real.arccos (toReal (clampOne x)) := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin,
      arcsin_clampOne]
  rw [hac, arccos_eq_two_mul hc.1 hc.2]
  have hw : (1 - toReal (clampOne x)) / 2 ≤ toReal (half (subUp one (clampOne x))) := by
    have := sub_le_subUp (one : 𝕋) (clampOne x)
    rw [toReal_one] at this; rw [toReal_half]; linarith
  have hs := le_trans (Real.sqrt_le_sqrt hw) (le_sqrtUp k _)
  have ha := le_trans (Real.arcsin_le_arcsin hs) (le_asinUp n k _)
  have := add_le_addUp (asinUp n k (sqrtUp k (half (subUp one (clampOne x)))))
    (asinUp n k (sqrtUp k (half (subUp one (clampOne x)))))
  simp only [acosUp]
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
