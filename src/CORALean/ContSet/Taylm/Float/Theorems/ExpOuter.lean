import CORALean.ContSet.Taylm.Float.Operations.Exp
import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
import CORALean.Global.TaylorRemainder
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# `Taylm.exp` encloses `exp ∘ f`

`taylor_remainder_abs_le` at `exp`, then every factor of the bound below its rounding.
`hp` is `expUp`'s range hypothesis at the top of the hull, as `Interval.exp_outer` keeps
it; it covers the centre too.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exp_outer (p : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hp : toReal (maximum T.constCoef T.bounds.2) ≤ 2 ^ p / 2) :
    (T.exp p).Encloses fun t => Real.exp (f t) := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  have hmax : toReal (maximum c T.bounds.2) = max (toReal c) (toReal T.bounds.2) :=
    toReal_maximum _ _
  have hc : toReal c ≤ 2 ^ p / 2 := le_trans (le_max_left _ _) (hmax ▸ hp)
  have hcoef := divFact_mem (expDown p c, expUp p c) (Real.exp_pos (toReal c)).le
    ⟨expDown_le p c, le_expUp p c hc⟩
  refine Taylm.compose_outer h Real.exp c _ _ N _
    (fun k => Real.exp (toReal c) / (k.factorial : ℝ))
    (fun k _ => hcoef k) fun t ht => ?_
  have hb := Taylm.bounds_mem h ht
  -- Lagrange at the centre, the derivative bounded at the top of the hull
  have hL := taylor_remainder_abs_le (g := Real.exp) (N := N) (c := toReal c)
    (x := f t) (D := Real.exp (max (toReal c) (toReal T.bounds.2)))
    (fun ξ _ => Real.contDiff_exp.contDiffAt) fun ξ hξ => by
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (le_trans hξ.2 (sup_le_sup_left hb.2 _))
  have hsum : ∑ k ∈ Finset.range (N + 1), iteratedDeriv k Real.exp (toReal c)
        / (k.factorial : ℝ) * (f t - toReal c) ^ k
      = ∑ k ∈ Finset.range (N + 1), Real.exp (toReal c) / (k.factorial : ℝ)
        * (f t - toReal c) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  rw [hsum] at hL
  refine le_trans hL ?_
  -- each factor of the bound below its rounded counterpart
  set B : 𝕋 := maximum zero (maximum (subUp T.bounds.2 c) (subUp c T.bounds.1))
  have hB : |f t - toReal c| ≤ toReal B := by
    have h1 := sub_le_subUp T.bounds.2 c
    have h2 := sub_le_subUp c T.bounds.1
    simp only [B, toReal_maximum, toReal_zero]
    rw [abs_le]
    constructor
    · linarith [le_max_right (0 : ℝ)
          (max (toReal (subUp T.bounds.2 c)) (toReal (subUp c T.bounds.1))),
        le_max_right (toReal (subUp T.bounds.2 c)) (toReal (subUp c T.bounds.1)), hb.1]
    · linarith [le_max_right (0 : ℝ)
          (max (toReal (subUp T.bounds.2 c)) (toReal (subUp c T.bounds.1))),
        le_max_left (toReal (subUp T.bounds.2 c)) (toReal (subUp c T.bounds.1)), hb.2]
  have hPow := le_powUp (abs_nonneg _) hB (N + 1)
  -- the derivative bound, the power and `1 / (N+1)!`, each below its rounding
  have hD : Real.exp (max (toReal c) (toReal T.bounds.2))
      ≤ toReal (expUp p (maximum c T.bounds.2)) := by
    rw [← hmax]; exact le_expUp p _ hp
  have hF := (divFact_mem ((one : 𝕋), (one : 𝕋)) zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (N + 1)).2
  have hE := Real.exp_pos (max (toReal c) (toReal T.bounds.2))
  have hY := pow_nonneg (abs_nonneg (f t - toReal c)) (N + 1)
  have hFpos : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
  -- the product of the three, rounded up twice
  calc Real.exp (max (toReal c) (toReal T.bounds.2)) * |f t - toReal c| ^ (N + 1)
        / ((N + 1).factorial : ℝ)
      = Real.exp (max (toReal c) (toReal T.bounds.2)) * |f t - toReal c| ^ (N + 1)
        * (1 / ((N + 1).factorial : ℝ)) := by ring
    _ ≤ toReal (expUp p (maximum c T.bounds.2)) * toReal (powUp B (N + 1))
        * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 := by
      apply mul_le_mul (mul_le_mul hD hPow hY (le_trans hE.le hD)) hF hFpos
      exact mul_nonneg (le_trans hE.le hD) (le_trans hY hPow)
    _ ≤ toReal (mulUp (expUp p (maximum c T.bounds.2)) (powUp B (N + 1)))
        * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 := by
      apply mul_le_mul_of_nonneg_right (mul_le_mulUp _ _) (le_trans hFpos hF)
    _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
