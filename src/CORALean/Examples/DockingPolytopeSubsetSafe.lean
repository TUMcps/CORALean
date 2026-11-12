module

public import CORALean.Examples.DockingPolytope
public import CORALean.Global.AddDivSqrtTwoLeSqrt
public import CORALean.ContSet.HPolytope.Real.Theorems.RegularPolygonSubsetBall

@[expose] public section

/-!
# The Docking polytope lies inside the safe set

Cauchy-Schwarz gives `(sx + sy)/√2 ≤ ‖s‖₂`; the regular `N`-gon gives
`maxₖ (cos φₖ, sin φₖ) · v ≥ cos(π/N) ‖v‖₂`. So a point of the polytope has
`cos(π/N) ‖v‖₂ ≤ 0.2 c + w (sx + sy)`, at most `cos(π/N) (0.2 + 2n ‖s‖₂)` where `sx + sy ≥ 0`
and at most `0.2 c` where `sx + sy < 0`, as `w ≥ 0`. The shrink of `w` below `c · 2n/√2` is
therefore conservative everywhere, not only on `sx + sy ≥ 0`. The row lemma
`dockingDist_le_of_row` takes the direction bound as a hypothesis, which the float polytope of
`DockingPolytopeFloatSubsetSafe` supplies with its rounded coefficients.

## Inputs
* `N` – number of sides
* `n` – mean motion
* `c` – radius factor of the polygon
* `w` – weight of `sx + sy`

## Hypotheses
* `hN` – the polygon has at least three sides
* `hn` – the mean motion is not negative
* `hc` – `c` is at most `cos(π/N)`
* `hw₀` – `w` is not negative
* `hw` – `w` is at most `c · 2n/√2`

## Conclusion
* every point of the polytope satisfies `‖v‖₂ ≤ 0.2 + 2n ‖s‖₂`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

/-- One row of the polytope bounds `‖v‖₂` by the safe set, given the bound of its direction. -/
theorem dockingDist_le_of_row {n κ c w β v₁ v₂ s₁ s₂ a b : ℝ}
    (hn : 0 ≤ n) (hκ : 0 < κ) (hcκ : c ≤ κ) (hw₀ : 0 ≤ w) (hw : w ≤ c * (2 * n / √2))
    (hβ : β ≤ 1 / 5 * c) (hdot : κ * √(v₁ ^ 2 + v₂ ^ 2) ≤ a * v₁ + b * v₂)
    (hrow : a * v₁ + b * v₂ + (-w) * s₁ + (-w) * s₂ ≤ β) : -- --- CONCL ---
    √(v₁ ^ 2 + v₂ ^ 2) ≤ 1 / 5 + 2 * n * √(s₁ ^ 2 + s₂ ^ 2) := by -- --- PROOF ---
  set V := √(v₁ ^ 2 + v₂ ^ 2) with hV
  set S := √(s₁ ^ 2 + s₂ ^ 2) with hS
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr two_pos
  have hcs := add_div_sqrt_two_le_sqrt s₁ s₂
  -- the row at the direction of `v`: `κ ‖v‖₂ ≤ 0.2 c + w (sx + sy)`
  have hkey : κ * V ≤ 1 / 5 * c + w * (s₁ + s₂) := by linarith
  have hκV : 0 ≤ κ * V := mul_nonneg hκ.le hV0
  have hnS : 0 ≤ 2 * n * S := by positivity
  by_cases ht : 0 ≤ s₁ + s₂
  · -- `sx + sy ≥ 0`: `w (sx + sy) ≤ c · 2n ‖s‖₂` by Cauchy-Schwarz
    have hm : 0 ≤ 2 * n / √2 := by positivity
    have hmt : 2 * n / √2 * (s₁ + s₂) ≤ 2 * n * S := by
      have : 2 * n / √2 * (s₁ + s₂) = 2 * n * ((s₁ + s₂) / √2) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hcs (by positivity)
    have hwt : w * (s₁ + s₂) ≤ c * (2 * n / √2) * (s₁ + s₂) := mul_le_mul_of_nonneg_right hw ht
    by_cases hc : 0 ≤ c
    · have h3 : c * (2 * n / √2 * (s₁ + s₂)) ≤ c * (2 * n * S) :=
        mul_le_mul_of_nonneg_left hmt hc
      have h4 : c * (1 / 5 + 2 * n * S) ≤ κ * (1 / 5 + 2 * n * S) :=
        mul_le_mul_of_nonneg_right hcκ (by positivity)
      have h5 : κ * V ≤ κ * (1 / 5 + 2 * n * S) := by
        have h6 : c * (2 * n / √2) * (s₁ + s₂) = c * (2 * n / √2 * (s₁ + s₂)) := by ring
        linarith
      exact le_of_mul_le_mul_left h5 hκ
    · -- a negative `c` leaves `κ ‖v‖₂ ≤ 0.2 c < 0`, which cannot be
      rw [not_le] at hc
      have h3 : c * (2 * n / √2) * (s₁ + s₂) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc.le hm) ht
      linarith
  · -- `sx + sy < 0`: `w (sx + sy) ≤ 0`, so `‖v‖₂ ≤ 0.2`
    rw [not_le] at ht
    have h3 : w * (s₁ + s₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw₀ ht.le
    have h4 : κ * V ≤ κ * (1 / 5) := by linarith
    linarith [le_of_mul_le_mul_left h4 hκ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Docking polytope lies inside the safe set. -/
theorem dockingPolytope_subset_safe {N : ℕ} {n c w : ℝ} (hN : 3 ≤ N) (hn : 0 ≤ n)
    (hc : c ≤ Real.cos (Real.pi / N)) (hw₀ : 0 ≤ w) (hw : w ≤ c * (2 * n / √2)) : -- --- CONCL ---
    (dockingPolytope N c w).toSet ⊆ dockingSafeSet n := by -- --- PROOF ---
  intro x hx
  rw [dockingPolytope, Real.HPolytope.mem_ineqs_iff] at hx
  -- the cosine of the half step is positive for three or more sides
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hκ : 0 < Real.cos (Real.pi / N) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [div_pos hpi (by linarith : (0 : ℝ) < N)], ?_⟩
    exact div_lt_div_of_pos_left hpi two_pos (by linarith)
  -- a direction of the polygon within half a step of `v`
  obtain ⟨k, hk⟩ := exists_regularPolygon_dot_ge (by omega : 0 < N) (x 2) (x 3)
  have hrow := hx k
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] at hrow
  exact dockingDist_le_of_row hn hκ hc hw₀ hw le_rfl hk (by linarith)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
