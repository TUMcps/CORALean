module

public import CORALean.ContSet.Taylm.Float.Operations.Log
public import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
public import CORALean.ContSet.Taylm.Float.Theorems.LogCoefMem
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.log_outer (q s : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hpos : 0 < toReal (minimum T.constCoef T.bounds.inf)) :
    (T.log q s).Encloses fun t => Real.log (f t) := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  rw [toReal_minimum] at hpos
  have hc : 0 < toReal c := lt_of_lt_of_le hpos (min_le_left _ _)
  refine Taylm.compose_outer h Real.log c _ _ N _
    (fun k => iteratedDeriv k Real.log (toReal c) / (k.factorial : ℝ))
    (fun k _ => Taylm.logCoef_mem q s hc k) fun t ht => ?_
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
