module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A zonotope as an ellipsoid

The coefficient domains differ only in the norm they bound: a zonotope's cube is
`‖β‖∞ ≤ 1`, an ellipsoid's ball is `‖u‖₂ ≤ 1`, and the cube sits inside `√h`
times the ball. So the same generators scaled by `√h` enclose, and the only
square root is that one scalar — which is the whole reason the generator form is
worth storing.

Loose by a factor of `√h` in the worst direction and exact in none, since a
zonotope is not an ellipsoid. Tighter enclosures exist — CORA's are the
minimum-volume and minimum-trace ones — and both are optimisation problems
rather than conversions. This one is the initial ellipse `E₀ = (m/2) G Gᵀ` of [2, Sec. 4.1].

CORA's `'outer:norm'` and `'inner:norm'` are [1, Thm. 1] and [1, Thm. 3]: shape `r E₀` for a
factor `F` of the initial guess `E₀ = F Fᵀ` (`m G Gᵀ` and `G Gᵀ`) and a bound `r` on the maximum,
or below the minimum, norm of `F⁻¹ Z` ([1, Def. 3], [1, Def. 4]). `ellipsoidNorm` and
`ellipsoidInnerNorm` take `F` and `r`; the guarantees hold for every invertible `F`, the paper's
`E₀^{-1/2}` among them, and every bound — exact or `[1, Lemma 3]`'s.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each coefficient contributes at most `1/h` of the ball's budget, so `h` of
them fit exactly. -/
theorem Zonotope.aux_coeff_sq_le {Z : Zonotope (Vec ℝ n)} {β : Fin Z.h → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (j : Fin Z.h) :
    (β j / Real.sqrt Z.h) ^ 2 ≤ 1 / (Z.h : ℝ) := by -- --- PROOF ---
  have hh : (0:ℝ) < (Z.h : ℝ) := by exact_mod_cast j.pos
  have hsq : Real.sqrt (Z.h : ℝ) ^ 2 = (Z.h : ℝ) := Real.sq_sqrt (le_of_lt hh)
  have hb : β j ^ 2 ≤ 1 := by
    rw [← sq_abs]
    calc |β j| ^ 2 = |β j| * |β j| := pow_two _
      _ ≤ 1 * 1 := mul_le_mul (hβ j) (hβ j) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [div_pow, hsq, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (le_of_lt (inv_pos.mpr hh))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ellipsoid_contains (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.ellipsoid.construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hxeq⟩ := Zonotope.mem_construct_iff.mp hx
  refine ⟨fun j => β j / Real.sqrt Z.h, ?_, ?_⟩
  -- `h` coefficients each within `1/h` of the budget fill the ball exactly
  · have hsum : ∑ j : Fin Z.h, (β j / Real.sqrt Z.h) ^ 2 ≤ 1 := by
      calc ∑ j : Fin Z.h, (β j / Real.sqrt Z.h) ^ 2
          ≤ ∑ _j : Fin Z.h, 1 / (Z.h : ℝ) :=
            Finset.sum_le_sum fun j _ => Zonotope.aux_coeff_sq_le hβ j
        _ = (Z.h : ℝ) * (1 / (Z.h : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 1 := by
            rcases Nat.eq_zero_or_pos Z.h with h0 | h0
            · rw [h0]
              norm_num
            · have hh : (0:ℝ) < (Z.h : ℝ) := by exact_mod_cast h0
              refine le_of_eq ?_
              rw [mul_one_div, div_self (ne_of_gt hh)]
    calc ‖fun j => β j / Real.sqrt Z.h‖₂ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  -- and the value: the `√h` in the generator cancels the one in the coefficient
  · funext i
    show x i = Z.c i + ∑ j, Real.sqrt Z.h * Z.G j i * (β j / Real.sqrt Z.h)
    rw [hxeq i]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    have hne : Real.sqrt (Z.h : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast j.pos))
    field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
