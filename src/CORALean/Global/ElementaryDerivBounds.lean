module

public import CORALean.Global.CoeffDomination
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Bounds on the high derivatives of the trigonometric and hyperbolic functions

What a Lagrange remainder needs of `sin`, `cos`, `sinh`, `cosh`, `tanh`, `tan`, `atan`,
`asin` and `acos`: a bound on `|g⁽ᴺ⁺¹⁾|` over a range of known magnitude. `sin` and `cos` are
bounded by one, `sinh` and `cosh` by `cosh` of the magnitude. The others have no closed form for
a high derivative, so it is a polynomial built by recursion from the differential equation
(`tanh' = 1 - tanh²`, `tan' = 1 + tan²`, `atan' = w`, `w' = -2x w²`, `asin' = v`, `v' = x v³`),
and the bound is that recursion run on absolute values of its coefficients, evaluated at the
magnitude.

## Inputs
* `q` – polynomial of the differential equation

## Output
* the function giving the polynomial that is each derivative order of a solution
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Polynomial


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The value at `y` is bounded by the dominating polynomial at `|y|`. -/
theorem IsCoeffDom.aux_of_abs_le {P A : ℝ[X]} (h : IsCoeffDom P A) (y : ℝ) : -- --- CONCL ---
    |P.eval y| ≤ A.eval |y| := by -- --- PROOF ---
  have hdeg : P.natDegree ≤ A.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    -- `A.coeff j = 0` for `j > A.natDegree`, hence `|P.coeff j| ≤ 0`
    have hA : A.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hj
    exact abs_nonpos_iff.1 (hA ▸ h j)
  rw [eval_eq_sum_range' (n := A.natDegree + 1) (by omega),
    eval_eq_sum_range' (n := A.natDegree + 1) (by omega)]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul (h j) (le_refl _) (by positivity) (h.nonneg j)


/-- A dominating polynomial dominates itself. -/
theorem IsCoeffDom.aux_self_of_dom {P A : ℝ[X]} (h : IsCoeffDom P A) : IsCoeffDom A A := fun j => by
  rw [abs_of_nonneg (h.nonneg j)]


/-- Dominance is closed under a nonnegative scalar. -/
theorem IsCoeffDom.aux_smul_nat {P A : ℝ[X]} (h : IsCoeffDom P A) (m : ℝ) (hm : 0 ≤ m) :
    IsCoeffDom (C m * P) (C m * A) := fun j => by
  rw [coeff_C_mul, coeff_C_mul, abs_mul, abs_of_nonneg hm]
  exact mul_le_mul_of_nonneg_left (h j) hm


/-- Dominance is closed under the factor `X`. -/
theorem IsCoeffDom.aux_X_mul {P A : ℝ[X]} (h : IsCoeffDom P A) : IsCoeffDom (X * P) (X * A) :=
  (show IsCoeffDom X X from fun j => by
    rw [coeff_X]; split_ifs <;> simp).mul h


/-- Polynomials dominated coefficientwise. -/
theorem IsCoeffDom.aux_abs_eval_le {P A : ℝ[X]} (h : IsCoeffDom P A) {y m : ℝ} (hy : |y| ≤ m) :
    |P.eval y| ≤ A.eval m :=
  le_trans (h.aux_of_abs_le y) (h.aux_self_of_dom.eval_mono (abs_nonneg _) hy)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial in `g` that is the `k`-th derivative of a `g` with `g' = q(g)`. -/
noncomputable def odePoly (q : ℝ[X]) : ℕ → ℝ[X]
  | 0 => X
  | k + 1 => derivative (odePoly q k) * q

/-- `atan⁽ʲ⁺¹⁾ x = atanPoly j x · (1 + x²)⁻⁽ʲ⁺¹⁾`. -/
noncomputable def atanPoly : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => derivative (atanPoly j) * (1 + X ^ 2) - C (2 * ((j : ℝ) + 1)) * (X * atanPoly j)

/-- `atanPoly` with every sign made positive. -/
noncomputable def atanDom : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => derivative (atanDom j) * (1 + X ^ 2) + C (2 * ((j : ℝ) + 1)) * (X * atanDom j)

/-- `asin⁽ʲ⁺¹⁾ x = asinPoly j x · (1 - x²)⁻⁽²ʲ⁺¹⁾ᐟ²`. -/
noncomputable def asinPoly : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => derivative (asinPoly j) * (1 - X ^ 2) + C (2 * (j : ℝ) + 1) * (X * asinPoly j)

/-- `asinPoly` with every sign made positive. -/
noncomputable def asinDom : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 => derivative (asinDom j) * (1 + X ^ 2) + C (2 * (j : ℝ) + 1) * (X * asinDom j)


-- the recursion on absolute coefficients dominates the recursion
/-- Domination of coefficients carries over to the ODE polynomials of `q` and `Q`. -/
theorem odePoly_dom {q Q : ℝ[X]} (h : IsCoeffDom q Q) (k : ℕ) :
    IsCoeffDom (odePoly q k) (odePoly Q k) := by
  induction k with
  | zero => exact fun j => by rw [odePoly, odePoly, coeff_X]; split_ifs <;> simp
  | succ k ih => exact ih.derivative.mul h

-- the constant `1` dominates itself
/-- The polynomial `1` dominates itself. -/
theorem one_dom : IsCoeffDom (1 : ℝ[X]) 1 := fun j => by
  rw [coeff_one]; split_ifs <;> simp

-- `1 - X²` is dominated by `1 + X²`
/-- `1 + X²` dominates `1 - X²` coefficientwise. -/
theorem one_sub_sq_dom : IsCoeffDom (1 - X ^ 2 : ℝ[X]) (1 + X ^ 2) := fun j => by
  simp only [coeff_sub, coeff_add, coeff_one, coeff_X_pow]
  split_ifs <;> simp_all

-- `1 + X²` dominates itself
/-- `1 + X²` dominates itself. -/
theorem one_add_sq_dom : IsCoeffDom (1 + X ^ 2 : ℝ[X]) (1 + X ^ 2) := fun j => by
  simp only [coeff_add, coeff_one, coeff_X_pow]
  split_ifs <;> simp_all

-- `atanDom` dominates `atanPoly`
/-- `atanDom j` dominates `atanPoly j` coefficientwise. -/
theorem atanPoly_dom (j : ℕ) : -- --- CONCL ---
    IsCoeffDom (atanPoly j) (atanDom j) := by -- --- PROOF ---
  induction j with
  | zero => exact one_dom
  | succ j ih =>
    rw [atanPoly, atanDom, sub_eq_add_neg]
    exact (ih.derivative.mul one_add_sq_dom).add ((ih.aux_X_mul.aux_smul_nat _ (by positivity)).neg)

-- `asinDom` dominates `asinPoly`
/-- The derivative polynomial of arcsine is dominated coefficientwise by `asinDom`. -/
theorem asinPoly_dom (j : ℕ) : -- --- CONCL ---
    IsCoeffDom (asinPoly j) (asinDom j) := by -- --- PROOF ---
  induction j with
  | zero => exact one_dom
  | succ j ih =>
    rw [asinPoly, asinDom]
    exact (ih.derivative.mul one_sub_sq_dom).add (ih.aux_X_mul.aux_smul_nat _ (by positivity))

-- each derivative of `sin` is `sin` shifted by a quarter period
/-- The `k`-th derivative of sine is sine shifted by `k` quarter periods. -/
theorem iteratedDeriv_sin_eq (k : ℕ) : -- --- CONCL ---
    iteratedDeriv k Real.sin = fun x => Real.sin (x + k * (Real.pi / 2)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h := ((hasDerivAt_id x).add_const (k * (Real.pi / 2))).sin
    simp only [id] at h
    rw [h.deriv, ← Real.sin_add_pi_div_two]
    simp only [mul_one]
    congr 1
    push_cast
    ring

-- each derivative of `cos` is `cos` shifted by a quarter period
/-- The `k`-th derivative of cosine is cosine shifted by `k` quarter periods. -/
theorem iteratedDeriv_cos_eq (k : ℕ) : -- --- CONCL ---
    iteratedDeriv k Real.cos = fun x => Real.cos (x + k * (Real.pi / 2)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h := ((hasDerivAt_id x).add_const (k * (Real.pi / 2))).cos
    simp only [id] at h
    rw [h.deriv]
    have := Real.cos_add_pi_div_two (x + k * (Real.pi / 2))
    simp only [mul_one]
    rw [← neg_neg (Real.sin _), ← this]
    push_cast
    ring_nf

-- the derivatives of `sinh` and `cosh` alternate between the two
/-- The `k`-th derivatives of `sinh` and `cosh` are `sinh` and `cosh` in the same or in the swapped
order. -/
theorem iteratedDeriv_sinh_cosh (k : ℕ) : -- --- CONCL ---
    (iteratedDeriv k Real.sinh = Real.sinh ∧ iteratedDeriv k Real.cosh = Real.cosh) ∨
    (iteratedDeriv k Real.sinh = Real.cosh ∧
      iteratedDeriv k Real.cosh = Real.sinh) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Real.deriv_sinh, Real.deriv_cosh]; right; exact ⟨rfl, rfl⟩
    · rw [h1, h2, Real.deriv_sinh, Real.deriv_cosh]; left; exact ⟨rfl, rfl⟩

-- `|sinh| ≤ cosh`, from `cosh ± sinh = exp (±x)`
/-- `|sinh x|` is at most `cosh x`. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h1 := Real.cosh_sub_sinh x
  have h2 := Real.cosh_add_sinh x
  rw [abs_le]
  constructor <;> nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

-- `tanh' = 1 - tanh²`, from the quotient `sinh / cosh`
/-- `tanh` has derivative `1 - tanh² x`. -/
theorem hasDerivAt_tanh (x : ℝ) : -- --- CONCL ---
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by -- --- PROOF ---
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  have e : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext fun x => Real.tanh_eq_sinh_div_cosh x
  rw [e]
  refine h.congr_deriv ?_
  beta_reduce
  have := Real.cosh_sq x
  have hc := (Real.cosh_pos x).ne'
  field_simp

-- `tanh` is smooth, being a quotient by `cosh`, which is positive
/-- `tanh` is smooth. -/
theorem contDiff_tanh {k : WithTop ℕ∞} : ContDiff ℝ k Real.tanh := by
  have e : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [e]
  exact Real.contDiff_sinh.div Real.contDiff_cosh fun x => (Real.cosh_pos x).ne'

-- where `g' = q(g)`, the `k`-th derivative is `odePoly q k` at `g`
/-- If `g' = q(g)` on an open set, the `k`-th derivative of `g` is the `k`-th ODE polynomial of `q`
evaluated at `g`. -/
theorem iteratedDeriv_of_ode {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {q : ℝ[X]}
    (hg : ∀ x ∈ U, HasDerivAt g (q.eval (g x)) x) (k : ℕ) : -- --- CONCL ---
    ∀ x ∈ U, iteratedDeriv k g x = (odePoly q k).eval (g x) := by -- --- PROOF ---
  induction k with
  | zero => intro x _; simp [odePoly]
  | succ k ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k g =ᶠ[nhds x] fun y => (odePoly q k).eval (g y) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) ih
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun y => (odePoly q k).eval (g y))
        ((derivative (odePoly q k)).eval (g x) * q.eval (g x)) x :=
      ((odePoly q k).hasDerivAt (g x)).comp x (hg x hx)
    rw [h2.deriv, odePoly, eval_mul]

-- `tanh⁽ᵏ⁾` is at most `odePoly (1 + X²) k` at one
/-- The `k`-th derivative of `tanh` is bounded by the `k`-th ODE polynomial of `1 + X²` at `1`. -/
theorem abs_iteratedDeriv_tanh_le (k : ℕ) (x : ℝ) : -- --- CONCL ---
    |iteratedDeriv k Real.tanh x| ≤ (odePoly (1 + X ^ 2) k).eval 1 := by -- --- PROOF ---
  have h := iteratedDeriv_of_ode (g := Real.tanh) (U := Set.univ) isOpen_univ
    (q := 1 - X ^ 2) (fun x _ => by simpa using hasDerivAt_tanh x) k x trivial
  rw [h]
  refine (odePoly_dom one_sub_sq_dom k).aux_abs_eval_le ?_
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x)]
  exact (div_le_one (Real.cosh_pos x)).2 (abs_sinh_le_cosh x)

-- `|tan x| ≤ tan m` for `|x| ≤ m < π/2`, by monotonicity and oddness
/-- `|tan x|` is at most `tan m` for `|x| ≤ m < π/2`. -/
theorem abs_tan_le {x m : ℝ} (hx : |x| ≤ m) (hm : m < Real.pi / 2) : -- --- CONCL ---
    |Real.tan x| ≤ Real.tan m := by -- --- PROOF ---
  have hm0 : 0 ≤ m := le_trans (abs_nonneg x) hx
  have hmono : ∀ y z : ℝ, 0 ≤ y → y ≤ z → z < Real.pi / 2 → Real.tan y ≤ Real.tan z :=
    fun y z hy hyz hz => Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos], by linarith⟩ ⟨by linarith [Real.pi_pos], hz⟩ hyz
  rcases abs_cases x with ⟨e, h0⟩ | ⟨e, h0⟩
  · rw [abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two h0 (by linarith))]
    exact hmono _ _ h0 (by linarith) hm
  · rw [← abs_neg, ← Real.tan_neg,
      abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))]
    exact hmono _ _ (by linarith) (by linarith) hm

-- `tan⁽ᵏ⁾` is at most `odePoly (1 + X²) k` at `tan m`
/-- The `k`-th derivative of `tan` on `|x| ≤ m < π/2` is bounded by the `k`-th ODE polynomial of `1
+ X²` at `tan m`. -/
theorem abs_iteratedDeriv_tan_le (k : ℕ) {x m : ℝ} (hx : |x| ≤ m)
    (hm : m < Real.pi / 2) : -- --- CONCL ---
    |iteratedDeriv k Real.tan x| ≤ (odePoly (1 + X ^ 2) k).eval (Real.tan m) := by -- --- PROOF ---
  have hxm : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hx; constructor <;> linarith [hx.1, hx.2]
  have h := iteratedDeriv_of_ode (g := Real.tan) (U := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    isOpen_Ioo (q := 1 + X ^ 2) (fun y hy => by
      have hc : Real.cos y ≠ 0 := (Real.cos_pos_of_mem_Ioo hy).ne'
      simpa [one_div, ← Real.inv_one_add_tan_sq hc] using Real.hasDerivAt_tan hc) k x hxm
  rw [h]
  refine (odePoly_dom one_add_sq_dom k).aux_abs_eval_le ?_
  exact abs_tan_le hx hm

-- derivatives of `(1 + x²)⁻¹` are `atanPoly j` times a power of it
/-- The `j`-th derivative of `1/(1 + x²)` is a polynomial times a power of `1/(1 + x²)`. -/
theorem iteratedDeriv_inv_one_add_sq (j : ℕ) : -- --- CONCL ---
    iteratedDeriv j (fun x : ℝ => (1 + x ^ 2)⁻¹)
      = fun x => (atanPoly j).eval x * ((1 + x ^ 2)⁻¹) ^ (j + 1) := by -- --- PROOF ---
  induction j with
  | zero => funext x; simp [atanPoly]
  | succ j ih =>
    -- differentiate the product `P · w^(j+1)` and put both terms over `w^(j+2)`
    rw [iteratedDeriv_succ, ih]
    funext x
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have hq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have hw : HasDerivAt (fun y : ℝ => (1 + y ^ 2)⁻¹) (-(2 * x) * ((1 + x ^ 2)⁻¹) ^ 2) x := by
      refine (hq.inv hne).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
    have h : HasDerivAt (fun y => (atanPoly j).eval y * ((1 + y ^ 2)⁻¹) ^ (j + 1)) _ x :=
      ((atanPoly j).hasDerivAt x).mul (hw.pow (j + 1))
    rw [h.deriv, atanPoly]
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_add, eval_pow, eval_one,
      Nat.add_sub_cancel]
    push_cast
    have hq : (1 + x ^ 2) * (1 + x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hne
    generalize (1 + x ^ 2)⁻¹ = w at *
    linear_combination (-(eval x (derivative (atanPoly j)) * w ^ (j + 1))) * hq

-- the same for `atan⁽ʲ⁺¹⁾`, one derivative further
/-- The `(j+1)`-th derivative of arctangent is `atanPoly j` times a power of `1/(1 + x²)`. -/
theorem iteratedDeriv_atan (j : ℕ) (x : ℝ) :
    iteratedDeriv (j + 1) Real.arctan x
      = (atanPoly j).eval x * ((1 + x ^ 2)⁻¹) ^ (j + 1) := by
  rw [iteratedDeriv_succ', Real.deriv_arctan]
  simp only [one_div]
  exact congrFun (iteratedDeriv_inv_one_add_sq j) x

-- the power is at most one, the polynomial is bounded by `atanDom`
/-- The `(j+1)`-th derivative of arctangent on `|x| ≤ m` is bounded by `atanDom j` at `m`. -/
theorem abs_iteratedDeriv_atan_le (j : ℕ) {x m : ℝ} (hx : |x| ≤ m) : -- --- CONCL ---
    |iteratedDeriv (j + 1) Real.arctan x| ≤ (atanDom j).eval m := by -- --- PROOF ---
  rw [iteratedDeriv_atan, abs_mul, abs_pow]
  have h := (atanPoly_dom j).aux_abs_eval_le hx
  have hw : |(1 + x ^ 2)⁻¹| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  calc _ ≤ (atanDom j).eval m * 1 :=
        mul_le_mul h (pow_le_one₀ (abs_nonneg _) hw) (by positivity) (le_trans (abs_nonneg _) h)
    _ = _ := mul_one _

-- `((1 - x²)^(1/2))⁻¹` has derivative `x` times its cube
/-- On `(-1, 1)` the derivative of `1/√(1 - y²)` is `x` times the cube of `1/√(1 - x²)`. -/
theorem hasDerivAt_inv_sqrt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : -- --- CONCL ---
    HasDerivAt (fun y : ℝ => (√(1 - y ^ 2))⁻¹) (x * ((√(1 - x ^ 2))⁻¹) ^ 3) x := by -- --- PROOF ---
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 h1
  have hq : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  refine ((hq.sqrt h1.ne').inv hs.ne').congr_deriv ?_
  rw [inv_pow]
  field_simp

-- its `j`-th derivative on `(-1, 1)` is `asinPoly j` times a power of it
/-- On `(-1, 1)` the `j`-th derivative of `1/√(1 - y²)` is `asinPoly j` times a power of `1/√(1 -
x²)`. -/
theorem iteratedDeriv_inv_sqrt (j : ℕ) : -- --- CONCL ---
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, iteratedDeriv j (fun y : ℝ => (√(1 - y ^ 2))⁻¹) x
      = (asinPoly j).eval x * ((√(1 - x ^ 2))⁻¹) ^ (2 * j + 1) := by -- --- PROOF ---
  induction j with
  | zero => intro x _; simp [asinPoly]
  | succ j ih =>
    -- the inductive hypothesis holds on the open interval, so it differentiates
    intro x hx
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (fun y : ℝ => (√(1 - y ^ 2))⁻¹) =ᶠ[nhds x]
        fun y => (asinPoly j).eval y * ((√(1 - y ^ 2))⁻¹) ^ (2 * j + 1) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) ih
    rw [hev.deriv_eq]
    have h : HasDerivAt (fun y => (asinPoly j).eval y * ((√(1 - y ^ 2))⁻¹) ^ (2 * j + 1)) _ x :=
      ((asinPoly j).hasDerivAt x).mul ((hasDerivAt_inv_sqrt hx).pow (2 * j + 1))
    rw [h.deriv, asinPoly]
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one,
      Nat.add_sub_cancel]
    have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 h1
    have hq : (1 - x ^ 2) * ((√(1 - x ^ 2))⁻¹) ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt h1.le]; exact mul_inv_cancel₀ h1.ne'
    generalize (√(1 - x ^ 2))⁻¹ = v at *
    push_cast
    linear_combination (-(eval x (derivative (asinPoly j)) * v ^ (2 * j + 1))) * hq

-- bounded on `|x| ≤ m < 1` by `asinDom` and the power at `m`
/-- The `j`-th derivative of `1/√(1 - y²)` on `|x| ≤ m < 1` is bounded by `asinDom j` at `m` times a
power of `1/√(1 - m²)`. -/
theorem abs_iteratedDeriv_inv_sqrt_le (j : ℕ) {x m : ℝ} (hx : |x| ≤ m)
    (hm : m < 1) : -- --- CONCL ---
    |iteratedDeriv j (fun y : ℝ => (√(1 - y ^ 2))⁻¹) x|
      ≤ (asinDom j).eval m * ((√(1 - m ^ 2))⁻¹) ^ (2 * j + 1) := by -- --- PROOF ---
  have hxm : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hx; constructor <;> linarith [hx.1, hx.2]
  rw [iteratedDeriv_inv_sqrt j x hxm, abs_mul, abs_pow]
  have h := (asinPoly_dom j).aux_abs_eval_le hx
  have hx2 : x ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith [abs_nonneg x]
  have hv : |(√(1 - x ^ 2))⁻¹| ≤ (√(1 - m ^ 2))⁻¹ := by
    rw [abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (by linarith)))]
    exact inv_anti₀ (Real.sqrt_pos.2 hm2) (Real.sqrt_le_sqrt (by linarith))
  exact mul_le_mul h (pow_le_pow_left₀ (abs_nonneg _) hv _) (by positivity)
    (le_trans (abs_nonneg _) h)

-- `asin⁽ʲ⁺¹⁾` is the `j`-th derivative of that function
/-- The `(j+1)`-th derivative of arcsine on `|x| ≤ m < 1` has the bound of `1/√(1 - y²)`'s `j`-th
derivative. -/
theorem abs_iteratedDeriv_asin_le (j : ℕ) {x m : ℝ} (hx : |x| ≤ m) (hm : m < 1) :
    |iteratedDeriv (j + 1) Real.arcsin x|
      ≤ (asinDom j).eval m * ((√(1 - m ^ 2))⁻¹) ^ (2 * j + 1) := by
  rw [iteratedDeriv_succ', Real.deriv_arcsin]
  simp only [one_div]
  exact abs_iteratedDeriv_inv_sqrt_le j hx hm


-- every derivative of `sin` is at most one
/-- Every derivative of sine is at most `1` in absolute value. -/
theorem abs_iteratedDeriv_sin_le (k : ℕ) (x : ℝ) : |iteratedDeriv k Real.sin x| ≤ 1 := by
  rw [iteratedDeriv_sin_eq]; exact Real.abs_sin_le_one _

-- every derivative of `cos` is at most one
/-- Every derivative of cosine is at most `1` in absolute value. -/
theorem abs_iteratedDeriv_cos_le (k : ℕ) (x : ℝ) : |iteratedDeriv k Real.cos x| ≤ 1 := by
  rw [iteratedDeriv_cos_eq]; exact Real.abs_cos_le_one _

-- every derivative of `sinh` is at most `cosh m` on `|x| ≤ m`
/-- Every derivative of `sinh` on `|x| ≤ m` is at most `cosh m` in absolute value. -/
theorem abs_iteratedDeriv_sinh_le (k : ℕ) {x m : ℝ} (hx : |x| ≤ m) :
    |iteratedDeriv k Real.sinh x| ≤ Real.cosh m := by
  have hc : Real.cosh x ≤ Real.cosh m := Real.cosh_le_cosh.2 (hx.trans (le_abs_self m))
  rcases iteratedDeriv_sinh_cosh k with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · exact (abs_sinh_le_cosh x).trans hc
  · rw [abs_of_pos (Real.cosh_pos x)]; exact hc

-- every derivative of `cosh` is at most `cosh m` on `|x| ≤ m`
/-- Every derivative of `cosh` on `|x| ≤ m` is at most `cosh m` in absolute value. -/
theorem abs_iteratedDeriv_cosh_le (k : ℕ) {x m : ℝ} (hx : |x| ≤ m) :
    |iteratedDeriv k Real.cosh x| ≤ Real.cosh m := by
  have hc : Real.cosh x ≤ Real.cosh m := Real.cosh_le_cosh.2 (hx.trans (le_abs_self m))
  rcases iteratedDeriv_sinh_cosh k with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
  · rw [abs_of_pos (Real.cosh_pos x)]; exact hc
  · exact (abs_sinh_le_cosh x).trans hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
