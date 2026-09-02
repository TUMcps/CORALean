import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

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
rather than conversions.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

noncomputable def Zonotope.ellipsoid (Z : Zonotope (Vec ℝ n)) : Ellipsoid n where
  k := Z.h
  q := Z.c
  G := Matrix.of fun i j => Real.sqrt Z.h * Z.G j i

/-- Each coefficient contributes at most `1/h` of the ball's budget, so `h` of
them fit exactly. -/
theorem Zonotope.aux_coeff_sq_le {Z : Zonotope (Vec ℝ n)} {β : Fin Z.h → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (j : Fin Z.h) :
    (β j / Real.sqrt Z.h) ^ 2 ≤ 1 / (Z.h : ℝ) := by
  have hh : (0:ℝ) < (Z.h : ℝ) := by exact_mod_cast j.pos
  have hsq : Real.sqrt (Z.h : ℝ) ^ 2 = (Z.h : ℝ) := Real.sq_sqrt (le_of_lt hh)
  have hb : β j ^ 2 ≤ 1 := by
    rw [← sq_abs]
    calc |β j| ^ 2 = |β j| * |β j| := pow_two _
      _ ≤ 1 * 1 := mul_le_mul (hβ j) (hβ j) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [div_pow, hsq, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (le_of_lt (inv_pos.mpr hh))

theorem Zonotope.ellipsoid_outer (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.ellipsoid.construct := by
  intro x hx
  obtain ⟨β, hβ, hxeq⟩ := Zonotope.mem_construct_iff.mp hx
  refine ⟨fun j => β j / Real.sqrt Z.h, ?_, ?_⟩
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
  · funext i
    show x i = Z.c i + ∑ j, Real.sqrt Z.h * Z.G j i * (β j / Real.sqrt Z.h)
    rw [hxeq i]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    have hne : Real.sqrt (Z.h : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast j.pos))
    field_simp

end CORALean.Real
