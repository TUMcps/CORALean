module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionMeanSq
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The two selector equations cut out exactly the two branches

Appendix A.1 of [1, Thm. 1], as arithmetic. `α₁α₂ = 1` over the unit cube forces
`α₁ = α₂ = ±1`; at `+1` the selector polynomial collapses to `-f₂`, at `-1` to
`f₁(1 - ½f₂)`, and `1 - ½f₂ ≥ ½` because a mean of squares of factors in `[-1,1]`
lies in `[0,1]`. So one branch pins the second operand's factors to `0` and the
other the first's, and there is no third solution.

Stated over bare reals rather than over a factor vector, since that is all it is
about: the two counts enter only through the two means.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand
* `x` – first selector
* `y` – second selector
* `u` – factors of first operand
* `v` – factors of second operand

## Hypotheses
* `hx` – first selector is within the unit interval
* `hy` – second selector is within the unit interval
* `hv` – factors of second operand are within the unit interval

## Conclusion
* the selector equations hold exactly on the two branches

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A mean of squares is never negative. -/
theorem ConPolyZono.aux_meanSq_nonneg {p : ℕ} (a : Fin p → ℝ) :
    0 ≤ ConPolyZono.unionMeanSq a := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- Over the unit cube it is at most one, the empty block giving `0`. -/
theorem ConPolyZono.aux_meanSq_le_one {p : ℕ} {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) :
    ConPolyZono.unionMeanSq a ≤ 1 := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [ConPolyZono.unionMeanSq]
  -- each square is at most one, so the sum is at most the count
  · have hsum : ∑ k, (a k) ^ 2 ≤ (p : ℝ) := by
      calc ∑ k, (a k) ^ 2 ≤ ∑ _k : Fin p, (1:ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            have h := abs_le.mp (ha k)
            nlinarith [h.1, h.2]
        _ = (p : ℝ) := by simp
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    rw [ConPolyZono.unionMeanSq, inv_mul_le_iff₀ hppos]
    linarith

/-- It vanishes only where the whole block does. -/
theorem ConPolyZono.aux_meanSq_eq_zero {p : ℕ} {a : Fin p → ℝ}
    (h : ConPolyZono.unionMeanSq a = 0) (k : Fin p) : a k = 0 := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos p with hp | hp
  · exact absurd k.isLt (by omega)
  -- the count is invertible, so the square sum itself is zero
  · have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have hs : ∑ j, (a j) ^ 2 = 0 := by
      rw [ConPolyZono.unionMeanSq, mul_eq_zero] at h
      rcases h with h1 | h2
      · exact absurd h1 (by positivity)
      · exact h2
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))).mp hs k
      (Finset.mem_univ k)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_domain_iff {p₁ p₂ : ℕ} (x y : ℝ) (u : Fin p₁ → ℝ)
    (v : Fin p₂ → ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hv : ∀ k, |v k| ≤ 1) : -- --- CONCL ---
    (x * y = 1 ∧ (1 + x + 2⁻¹ * ConPolyZono.unionMeanSq u * (1 - x))
        * (1 - 2⁻¹ * ConPolyZono.unionMeanSq v) - y - 1 = 0)
      ↔ ((x = 1 ∧ y = 1 ∧ ∀ k, v k = 0)
        ∨ (x = -1 ∧ y = -1 ∧ ∀ k, u k = 0)) := by -- --- PROOF ---
  constructor
  · rintro ⟨hxy, hg⟩
    have hax := abs_le.mp hx
    have hay := abs_le.mp hy
    -- `xy = 1` inside the square `[-1,1]²` leaves only the two corners
    have hx1 : x = 1 ∨ x = -1 := by
      rcases lt_trichotomy x 1 with h | h | h
      · rcases lt_trichotomy x (-1) with h' | h' | h'
        · linarith [hax.1]
        · exact Or.inr h'
        · exfalso
          nlinarith [hay.1, hay.2, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x)
            (by linarith : (0:ℝ) ≤ 1 + y), mul_nonneg (by linarith : (0:ℝ) ≤ 1 + x)
            (by linarith : (0:ℝ) ≤ 1 - y), mul_pos (by linarith : (0:ℝ) < 1 - x)
            (by linarith : (0:ℝ) < 1 + x)]
      · exact Or.inl h
      · linarith [hax.2]
    rcases hx1 with rfl | rfl
    · -- at `+1` the polynomial is `-f₂`
      have hy1 : y = 1 := by linarith [hxy]
      subst hy1
      exact Or.inl ⟨rfl, rfl, fun k => ConPolyZono.aux_meanSq_eq_zero (by nlinarith [hg]) k⟩
    · -- at `-1` it is `f₁(1 - ½f₂)`, and the right factor is at least `½`
      have hy1 : y = -1 := by nlinarith [hxy]
      subst hy1
      refine Or.inr ⟨rfl, rfl, fun k => ConPolyZono.aux_meanSq_eq_zero ?_ k⟩
      nlinarith [hg, ConPolyZono.aux_meanSq_nonneg u, ConPolyZono.aux_meanSq_nonneg v,
        ConPolyZono.aux_meanSq_le_one hv]
  · rintro (⟨rfl, rfl, hv0⟩ | ⟨rfl, rfl, hu0⟩)
    · have h : ConPolyZono.unionMeanSq v = 0 := by
        simp only [ConPolyZono.unionMeanSq]
        rw [Finset.sum_eq_zero fun k _ => by rw [hv0 k]; ring]
        ring
      exact ⟨by ring, by rw [h]; ring⟩
    · have h : ConPolyZono.unionMeanSq u = 0 := by
        simp only [ConPolyZono.unionMeanSq]
        rw [Finset.sum_eq_zero fun k _ => by rw [hu0 k]; ring]
        ring
      exact ⟨by ring, by rw [h]; ring⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
