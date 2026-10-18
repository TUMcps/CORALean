module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope

@[expose] public section

/-!
# The a-posteriori Krylov error bound is linear in time

[1, Prop. B.1]: Wang and Ye's bound (32), `err(T) ≤ ‖v‖ h_{ξ+1,ξ} max_{[0,T]}|e_ξᵀe^{Ht}e₁|
(e^{νT} - 1)/ν` on `[0, t_f]`, gives `err(t) ≤ ‖v‖ ε_norm t`, `ε_norm = h_{ξ+1,ξ} ω ϕ`, for
any `ω` above the maximum (35) and `ϕ` as in (34). (32) is the hypothesis — [1] cites it — and
`(e^{νT} - 1)/ν` is read as `T` at `ν = 0`, its limit. The step is `(e^{νt} - 1)/(νt) ≤ ϕ`:
for `ν > 0` the slope of `exp` from `0` grows with `t` (convexity), for `ν ≤ 0` it is at
most `1` (`x + 1 ≤ eˣ`). [1]'s series argument for the sign of `ϕ̇` holds only for `ν > 0`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(e^{νt} - 1)/ν ≤ ϕ t`, and it is nonnegative, for `t ∈ [0, t_f]`. -/
theorem Krylov.aux_psi_le (ν : ℝ) {tf t : ℝ} (htf : 0 < tf) (ht0 : 0 ≤ t) (httf : t ≤ tf) :
    0 ≤ (if ν = 0 then t else (Real.exp (ν * t) - 1) / ν) ∧
    (if ν = 0 then t else (Real.exp (ν * t) - 1) / ν)
      ≤ (if 0 < ν then (Real.exp (ν * tf) - 1) / (ν * tf) else 1) * t := by -- --- PROOF ---
  rcases lt_trichotomy ν 0 with hν | hν | hν
  · -- `ν < 0`: `x + 1 ≤ eˣ` at `x = νt`
    rw [if_neg hν.ne, if_neg (not_lt.mpr hν.le), one_mul]
    have h1 := Real.add_one_le_exp (ν * t)
    have h2 : Real.exp (ν * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact ⟨div_nonneg_of_nonpos (by linarith) hν.le, (div_le_iff_of_neg hν).mpr (by nlinarith)⟩
  · subst hν
    simp only [if_true, lt_irrefl, if_false, one_mul]
    exact ⟨ht0, le_rfl⟩
  · -- `ν > 0`: the slope of `exp` from `0` grows
    rw [if_neg hν.ne', if_pos hν]
    have h1 := Real.add_one_le_exp (ν * t)
    refine ⟨div_nonneg (by nlinarith) hν.le, ?_⟩
    rcases ht0.eq_or_lt with rfl | htpos
    · simp
    have hsl := convexOn_exp.secant_mono (a := 0) (x := ν * t) (y := ν * tf) (mem_univ _)
      (mem_univ _) (mem_univ _) (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left httf hν.le)
    rw [Real.exp_zero, sub_zero, sub_zero] at hsl
    calc (Real.exp (ν * t) - 1) / ν = (Real.exp (ν * t) - 1) / (ν * t) * t := by
          field_simp
      _ ≤ (Real.exp (ν * tf) - 1) / (ν * tf) * t := mul_le_mul_of_nonneg_right hsl ht0


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.err_le_linear {err M : ℝ → ℝ} {a ω ν tf : ℝ} (htf : 0 < tf) (ha : 0 ≤ a)
    (hM0 : ∀ T ∈ Icc 0 tf, 0 ≤ M T) (hMω : ∀ T ∈ Icc 0 tf, M T ≤ ω)
    (h32 : ∀ T ∈ Icc 0 tf,
      err T ≤ a * M T * (if ν = 0 then T else (Real.exp (ν * T) - 1) / ν))
    {t : ℝ} (ht : t ∈ Icc 0 tf) : -- --- STMT ---
    err t ≤ a * ω * (if 0 < ν then (Real.exp (ν * tf) - 1) / (ν * tf) else 1)
      * t := by -- --- PROOF ---
  obtain ⟨hψ0, hψ⟩ := Krylov.aux_psi_le ν htf ht.1 ht.2
  have hMt := hMω t ht
  calc err t ≤ a * M t * (if ν = 0 then t else (Real.exp (ν * t) - 1) / ν) := h32 t ht
    _ ≤ a * ω * (if ν = 0 then t else (Real.exp (ν * t) - 1) / ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMt ha) hψ0
    _ ≤ a * ω * ((if 0 < ν then (Real.exp (ν * tf) - 1) / (ν * tf) else 1) * t) :=
        mul_le_mul_of_nonneg_left hψ (mul_nonneg ha ((hM0 t ht).trans hMt))
    _ = _ := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
