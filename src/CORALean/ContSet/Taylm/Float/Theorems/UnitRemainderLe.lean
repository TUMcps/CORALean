import CORALean.ContSet.Taylm.Float.Operations.UnitRemainder
import CORALean.ContSet.Taylm.Float.Theorems.AbsSubLeMaximumSubUp
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
import CORALean.Global.TaylorRemainder

/-!
# `Taylm.unitRemainder` bounds the Lagrange remainder of a function with bounded derivative

`taylor_remainder_abs_le` at the constant part with derivative bound one, then the reach and the
factorial below their roundings, as in `Taylm.exp_outer`.
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

theorem Taylm.unitRemainder_le {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {g : ℝ → ℝ} (hg : ∀ ξ, ContDiffAt ℝ (T.maxOrder + 1) g ξ)
    (hD : ∀ ξ, |iteratedDeriv (T.maxOrder + 1) g ξ| ≤ 1) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) :
    |g (f t) - ∑ k ∈ Finset.range (T.maxOrder + 1), iteratedDeriv k g (toReal T.constCoef)
      / (k.factorial : ℝ) * (f t - toReal T.constCoef) ^ k|
        ≤ toReal T.unitRemainder := by -- --- PROOF ---
  set c := T.constCoef
  set N := T.maxOrder
  have hb := Taylm.bounds_mem h ht
  have hL := taylor_remainder_abs_le (g := g) (N := N) (c := toReal c) (x := f t) (D := 1)
    (fun ξ _ => hg ξ) fun ξ _ => hD ξ
  refine le_trans hL ?_
  -- the reach of the hull from the centre, below its rounding
  set B : 𝕋 := maximum zero (maximum (subUp T.bounds.2 c) (subUp c T.bounds.1))
  have hB : |f t - toReal c| ≤ toReal B := abs_sub_le_maximum_subUp c hb.1 hb.2
  have hPow := le_powUp (abs_nonneg _) hB (N + 1)
  have hF := (divFact_mem ((one : 𝕋), (one : 𝕋)) zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) (N + 1)).2
  have hY := pow_nonneg (abs_nonneg (f t - toReal c)) (N + 1)
  have hFpos : (0 : ℝ) ≤ 1 / ((N + 1).factorial : ℝ) := by positivity
  -- the power and `1 / (N+1)!`, the product rounded up
  calc 1 * |f t - toReal c| ^ (N + 1) / ((N + 1).factorial : ℝ)
      = |f t - toReal c| ^ (N + 1) * (1 / ((N + 1).factorial : ℝ)) := by ring
    _ ≤ toReal (powUp B (N + 1)) * toReal (divFact ((one : 𝕋), (one : 𝕋)) (N + 1)).2 :=
      mul_le_mul hPow hF hFpos (le_trans hY hPow)
    _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
