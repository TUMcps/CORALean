module

public import CORALean.ContSet.Taylm.Float.Operations.Tanh
public import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
public import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Interval.Float.Theorems.EvalListMem
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.Global.ElementaryDerivBounds
public import CORALean.Global.TaylorRemainder

@[expose] public section

/-!
# `Taylm.tanh` encloses `tanh ∘ f`

`taylor_remainder_abs_le` at `tanh`, whose derivatives are `odePoly (1 - X²) k` at `tanh`
(`iteratedDeriv_of_ode`), bounded by `odePoly (1 + X²) (N+1)` at one. The integer polynomial
lists evaluate as the real ones (`eval_odePoly_odeL`), and `Interval.evalList_mem` encloses them.
`hp` is `tanhUp`'s range hypothesis at the centre.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Polynomial

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.tanh_outer (p : ℕ) {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hp : toReal T.constCoef ≤ 2 ^ p / 2) :
    (T.tanh p).Encloses fun t => Real.tanh (f t) := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  -- the derivatives of `tanh` at the centre are the integer polynomial at `tanh c`
  have hder : ∀ k : ℕ, iteratedDeriv k Real.tanh (toReal c) =
      evalL (odeL [1, 0, -1] k) (Real.tanh (toReal c)) := by
    intro k
    rw [iteratedDeriv_of_ode (g := Real.tanh) (U := Set.univ) isOpen_univ
      (q := 1 - X ^ 2) (fun x _ => by simpa using hasDerivAt_tanh x) k _ trivial]
    exact eval_odePoly_odeL (q := [1, 0, -1]) (fun x => by simp [evalL]; ring) k _
  have ht1 := tanhDown_le p c
  have ht2 := tanhUp_ge p c hp
  have hF1 := fun k => divFact_mem ((one : 𝕋), (one : 𝕋)) zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) k
  refine Taylm.compose_outer h Real.tanh c _ _ N _
    (fun k => iteratedDeriv k Real.tanh (toReal c) / (k.factorial : ℝ)) (fun k _ => ?_)
    fun t ht => ?_
  · -- coefficient `P(tanh c) * (1 / k!)` between the corner products
    have hb := Interval.evalList_mem ht1 ht2 (odeL [1, 0, -1] k)
    have hf := hF1 k
    have hs := Real.Interval.mul_between_corners hb.1 hb.2 hf.1 hf.2
    rw [← div_eq_mul_one_div, ← hder k] at hs
    exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hs.1, le_trans hs.2 (Interval.le_mulHi _ _ _ _)⟩
  · have hb := Taylm.bounds_mem h ht
    -- Lagrange at the centre, the derivative bounded by `odePoly (1 + X²) (N+1)` at one
    have hD1 : ∀ ξ : ℝ, |iteratedDeriv (N + 1) Real.tanh ξ| ≤
        evalL (odeL [1, 0, 1] (N + 1)) 1 := fun ξ => by
      rw [← eval_odePoly_odeL (q := [1, 0, 1]) (Q := 1 + X ^ 2)
        (fun x => by simp [evalL]; ring) _ 1]
      exact abs_iteratedDeriv_tanh_le _ ξ
    have hL := taylor_remainder_abs_le (g := Real.tanh) (N := N) (c := toReal c)
      (x := f t) (D := evalL (odeL [1, 0, 1] (N + 1)) 1)
      (fun ξ _ => contDiff_tanh.contDiffAt) fun ξ _ => hD1 ξ
    refine le_trans hL ?_
    -- each factor of the bound below its rounded counterpart
    set B : 𝕋 := maximum zero (maximum (subUp T.bounds.sup c) (subUp c T.bounds.inf))
    have hB : |f t - toReal c| ≤ toReal B := abs_sub_le_maximum_subUp c hb.1 hb.2
    have hPow := le_powUp (abs_nonneg _) hB (N + 1)
    -- the derivative bound below its rounding
    have hD : evalL (odeL [1, 0, 1] (N + 1)) 1 ≤
        toReal (Interval.evalList (one : 𝕋) one (odeL [1, 0, 1] (N + 1))).sup :=
      (Interval.evalList_mem (lo := (one : 𝕋)) (hi := one) (by rw [toReal_one])
        (by rw [toReal_one]) _).2
    -- the bound is non-negative, being above an absolute value
    have hE : 0 ≤ evalL (odeL [1, 0, 1] (N + 1)) 1 :=
      le_trans (abs_nonneg _) (hD1 0)
    have hF := (divFact_mem ((one : 𝕋), (one : 𝕋)) zero_le_one
      (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (N + 1)).2
    have hY := pow_nonneg (abs_nonneg (f t - toReal c)) (N + 1)
    have hFpos : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
    calc evalL (odeL [1, 0, 1] (N + 1)) 1 * |f t - toReal c| ^ (N + 1) / ((N + 1).factorial : ℝ)
        = evalL (odeL [1, 0, 1] (N + 1)) 1 * |f t - toReal c| ^ (N + 1)
          * (1 / ((N + 1).factorial : ℝ)) := by ring
      _ ≤ toReal (Interval.evalList (one : 𝕋) one (odeL [1, 0, 1] (N + 1))).sup
            * toReal (powUp B (N + 1))
          * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 := by
        apply mul_le_mul (mul_le_mul hD hPow hY (le_trans hE hD)) hF hFpos
        exact mul_nonneg (le_trans hE hD) (le_trans hY hPow)
      _ ≤ toReal (mulUp (Interval.evalList (one : 𝕋) one (odeL [1, 0, 1] (N + 1))).sup
            (powUp B (N + 1))) * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 := by
        apply mul_le_mul_of_nonneg_right (mul_le_mulUp _ _) (le_trans hFpos hF)
      _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
