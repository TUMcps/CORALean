module

public import CORALean.ContSet.Taylm.Float.Operations.Log
public import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.Global.TaylorRemainder

@[expose] public section

/-!
# `Taylm.log` encloses `log ∘ f`

Where the center and the bottom of the range are positive, as at the exact layer, here read
off the stored floats: `taylor_remainder_abs_le` at `log`, then every piece of the bound below
its rounding.

## Inputs
* `q` – precision of the exponential
* `s` – number of steps
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hpos` – the range stays positive

## Conclusion
* the result encloses the logarithm of the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Taylor coefficients of `log` at a positive point. -/
theorem Taylm.aux_log_coef {c : ℝ} (hc : 0 < c) (k : ℕ) : -- --- CONCL ---
    iteratedDeriv (k + 1) Real.log c / ((k + 1).factorial : ℝ)
      = (-1) ^ k * (1 / c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by -- --- PROOF ---
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv,
    show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    Nat.factorial_succ, Nat.cast_mul, one_div, inv_pow]
  have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp


/-- `aux_logCoef` encloses the Taylor coefficients of `log`. -/
theorem Taylm.aux_logCoef_mem (q s : ℕ) {c : 𝕋} (hc : 0 < toReal c) (k : ℕ) : -- --- CONCL ---
    toReal (Taylm.aux_logCoef q s c k).inf ≤ iteratedDeriv k Real.log (toReal c) / (k.factorial : ℝ)
      ∧ iteratedDeriv k Real.log (toReal c) / (k.factorial : ℝ)
        ≤ toReal (Taylm.aux_logCoef q s c k).sup := by -- --- PROOF ---
  have hinvU : 1 / toReal c ≤ toReal (divUp one c) := by
    have := div_le_divUp one c hc; rwa [toReal_one] at this
  have hinv0 : 0 < 1 / toReal c := by positivity
  cases k with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, Taylm.aux_logCoef,
      toReal_neg]
    constructor
    · -- `log c = -log (1/c) ≥ -log u ≥ -logUp u` for `u ≥ 1/c`
      have hu : 0 < toReal (divUp one c) := lt_of_lt_of_le hinv0 hinvU
      have h1 := le_logUp q s (divUp one c) hu
      have h2 := Real.log_le_log hinv0 hinvU
      rw [one_div, Real.log_inv] at h2
      linarith
    · exact le_logUp q s c hc
  | succ k =>
    rw [Taylm.aux_log_coef hc k]
    -- the magnitude `(1/c)^(k+1) / (k+1)` and its two roundings
    set m := (1 / toReal c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hU : ((k + 1 : ℕ) : ℝ) * 1 ≤ toReal (nsmulUp (k + 1) (one : 𝕋)) := by
      have := le_nsmulUp (k + 1) (one : 𝕋); rwa [toReal_one] at this
    have hD : toReal (nsmulDown (k + 1) (one : 𝕋)) ≤ ((k + 1 : ℕ) : ℝ) * 1 := by
      have := nsmulDown_le (k + 1) (one : 𝕋); rwa [toReal_one] at this
    have hUpos : (0 : ℝ) < toReal (nsmulUp (k + 1) (one : 𝕋)) := by linarith
    have hm : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) =
        max 1 (toReal (nsmulDown (k + 1) (one : 𝕋))) := by rw [toReal_maximum, toReal_one]
    have hm1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) := by
      rw [hm]; exact le_max_left _ _
    have hmk : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [hm]; exact max_le hk1 (by linarith)
    -- the lower end of `1/c`, floored at zero so the downward power stays monotone
    have hpw0 : 0 ≤ (1 / toReal c) ^ (k + 1) := pow_nonneg hinv0.le _
    have hL0 : 0 ≤ toReal (maximum zero (divDown one c)) := by
      rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
    have hL : toReal (maximum zero (divDown one c)) ≤ 1 / toReal c := by
      rw [toReal_maximum, toReal_zero]
      refine max_le hinv0.le ?_
      have := divDown_le_div one c hc; rwa [toReal_one] at this
    -- the two ends of the magnitude
    have hlo : toReal (divDown (powDown (maximum zero (divDown one c)) (k + 1))
        (nsmulUp (k + 1) one)) ≤ m := by
      refine le_trans (divDown_le_div _ _ hUpos) ?_
      calc toReal (powDown (maximum zero (divDown one c)) (k + 1))
            / toReal (nsmulUp (k + 1) (one : 𝕋))
          ≤ (1 / toReal c) ^ (k + 1) / toReal (nsmulUp (k + 1) (one : 𝕋)) :=
            div_le_div_of_nonneg_right (powDown_le hL0 hL _) hUpos.le
        _ ≤ m := div_le_div_of_nonneg_left hpw0 (by linarith) (by linarith)
    have hhi : m ≤ toReal (divUp (powUp (divUp one c) (k + 1))
        (maximum one (nsmulDown (k + 1) one))) := by
      refine le_trans ?_ (div_le_divUp _ _ (by linarith))
      calc m ≤ (1 / toReal c) ^ (k + 1) / toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) :=
            div_le_div_of_nonneg_left hpw0 (by linarith) hmk
        _ ≤ _ := div_le_div_of_nonneg_right (le_powUp hinv0.le hinvU _) (by linarith)
    -- the sign `(-1)^k`
    have hsplit : (-1 : ℝ) ^ k * (1 / toReal c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
        = (-1) ^ k * m := by simp only [m]; ring
    rw [hsplit]
    simp only [Taylm.aux_logCoef]
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos (Nat.even_iff.1 he), he.neg_one_pow, one_mul]
      exact ⟨hlo, hhi⟩
    · rw [if_neg (by rw [Nat.odd_iff.1 ho]; exact one_ne_zero), ho.neg_one_pow, toReal_neg,
        toReal_neg]
      constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.log_outer (q s : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hpos : 0 < toReal (minimum T.constCoef T.bounds.inf)) : -- --- CONCL ---
    (T.log q s).Encloses fun t => Real.log (f t) := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  rw [toReal_minimum] at hpos
  have hc : 0 < toReal c := lt_of_lt_of_le hpos (min_le_left _ _)
  refine Taylm.compose_outer h Real.log c _ _ N _
    (fun k => iteratedDeriv k Real.log (toReal c) / (k.factorial : ℝ))
    (fun k _ => Taylm.aux_logCoef_mem q s hc k) fun t ht => ?_
  have hb := Taylm.bounds_mem h ht
  set L := min (toReal c) (toReal T.bounds.inf)
  -- Lagrange at the center, the derivative bounded at the bottom of the hull
  have hL := taylor_remainder_abs_le (g := Real.log) (N := N) (c := toReal c)
    (x := f t) (D := (N.factorial : ℝ) / L ^ (N + 1))
    (fun ξ hξ => Real.contDiffAt_log.2 (ne_of_gt (lt_of_lt_of_le hpos
      (le_trans (inf_le_inf_left _ hb.1) hξ.1))))
    fun ξ hξ => by
      have hξL : L ≤ ξ := le_trans (inf_le_inf_left _ hb.1) hξ.1
      have hξ0 : 0 < ξ := lt_of_lt_of_le hpos hξL
      rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv,
        abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
        show (-1 - (N : ℤ)) = -((N + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_neg, zpow_natCast, abs_inv, abs_pow, abs_of_pos hξ0, div_eq_mul_inv]
      gcongr
  refine le_trans hL ?_
  -- `N!/Lᴺ⁺¹ · yᴺ⁺¹/(N+1)! = (y/L)ᴺ⁺¹/(N+1)`, then each piece below its rounding
  set B : 𝕋 := maximum zero (maximum (subUp T.bounds.sup c) (subUp c T.bounds.inf))
  have hB : |f t - toReal c| ≤ toReal B := abs_sub_le_maximum_subUp c hb.1 hb.2
  -- `B / L` rounded up, then its power, then the division by `N + 1`
  have hLf : toReal (minimum c T.bounds.inf) = L := toReal_minimum _ _
  have hq : |f t - toReal c| / L ≤ toReal (divUp B (minimum c T.bounds.inf)) := by
    refine le_trans ?_ (div_le_divUp _ _ (by rw [hLf]; exact hpos))
    rw [hLf]
    exact div_le_div_of_nonneg_right hB hpos.le
  have hpow := le_powUp (div_nonneg (abs_nonneg _) hpos.le) hq (N + 1)
  have hk1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hD : toReal (nsmulDown (N + 1) (one : 𝕋)) ≤ ((N + 1 : ℕ) : ℝ) * 1 := by
    have := nsmulDown_le (N + 1) (one : 𝕋); rwa [toReal_one] at this
  have hm : toReal (maximum one (nsmulDown (N + 1) (one : 𝕋))) =
      max 1 (toReal (nsmulDown (N + 1) (one : 𝕋))) := by rw [toReal_maximum, toReal_one]
  have hm1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown (N + 1) (one : 𝕋))) := by
    rw [hm]; exact le_max_left _ _
  have hmk : toReal (maximum one (nsmulDown (N + 1) (one : 𝕋))) ≤ ((N + 1 : ℕ) : ℝ) := by
    rw [hm]; exact max_le hk1 (by linarith)
  -- the identity that turns the Lagrange bound into the stored form
  have hX0 : 0 ≤ (|f t - toReal c| / L) ^ (N + 1) := by positivity
  have he : (N.factorial : ℝ) / L ^ (N + 1) * |f t - toReal c| ^ (N + 1)
      / ((N + 1).factorial : ℝ) = (|f t - toReal c| / L) ^ (N + 1) / ((N + 1 : ℕ) : ℝ) := by
    have : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    rw [Nat.factorial_succ, Nat.cast_mul, div_pow]
    field_simp
  rw [he]
  refine le_trans ?_ (div_le_divUp _ _ (by linarith))
  calc (|f t - toReal c| / L) ^ (N + 1) / ((N + 1 : ℕ) : ℝ)
      ≤ (|f t - toReal c| / L) ^ (N + 1) / toReal (maximum one (nsmulDown (N + 1) (one : 𝕋))) :=
        div_le_div_of_nonneg_left hX0 (by linarith) hmk
    _ ≤ _ := div_le_div_of_nonneg_right hpow (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
