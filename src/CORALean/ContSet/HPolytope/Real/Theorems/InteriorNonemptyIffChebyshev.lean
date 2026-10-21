module

public import CORALean.ContSet.ContSet.Theorems.InteriorEqEmptyIffForallBall
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# Non-degeneracy by the Chebyshev ball

[1, Eq. 18] decides degeneracy of `⟨A, b⟩` by the linear program [1, Eq. 19]: a ball of
radius `r` around `c` lies in the halfspace `A(j,·) x ≤ b(j)` exactly when
`A(j,·) c + r ‖A(j,·)‖₂ ≤ b(j)`. So the interior is nonempty exactly when some `r > 0` is
feasible: a degenerate nonempty polytope has optimal radius `0`, as the text says. The printed
display has the comparison the other way round (`⊤ if r > 0`); see
`ineqs_degenerate_chebyshev_counterexample`.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`

## Hypotheses
* none

## Conclusion
* the interior is nonempty iff a ball of positive radius fits in every halfspace

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A Euclidean ball lies in a halfspace exactly when its center does with `r ‖a‖₂` to spare. -/
theorem aux_ball_subset_iff (a c : Vec ℝ n) {r : ℝ} (hr : 0 ≤ r) (β : ℝ) : -- --- CONCL ---
    (∀ x : Vec ℝ n, ‖x‖₂ ≤ r → a ⬝ᵥ (c + x) ≤ β) ↔ a ⬝ᵥ c + r * ‖a‖₂ ≤ β := by -- --- PROOF ---
  constructor
  · intro h
    rcases (norm₂_nonneg a).eq_or_lt with ha | ha
    -- a zero normal: the center alone
    · have := h 0 (by rw [norm₂_zero]; exact hr)
      rw [add_zero] at this
      rw [← ha, mul_zero, add_zero]
      exact this
    -- otherwise the ball's farthest point along `a`
    · have hx : ‖(r / ‖a‖₂) • a‖₂ = r := by
        rw [norm₂_smul, abs_of_nonneg (div_nonneg hr ha.le), div_mul_cancel₀ _ ha.ne']
      have := h ((r / ‖a‖₂) • a) hx.le
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_self] at this
      have heq : r / ‖a‖₂ * ‖a‖₂ ^ 2 = r * ‖a‖₂ := by field_simp
      linarith
  · intro h x hx
    rw [dotProduct_add]
    have hcs := dotProduct_le_norm₂_mul_norm₂ a x
    have : ‖a‖₂ * ‖x‖₂ ≤ r * ‖a‖₂ := by
      rw [mul_comm r]
      exact mul_le_mul_of_nonneg_left hx (norm₂_nonneg a)
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_interior_nonempty_iff (A : Mat ℝ q n) (b : Vec ℝ q) : -- --- CONCL ---
    (interior (HPolytope.ineqs A b).construct).Nonempty ↔
      ∃ (c : Vec ℝ n) (r : ℝ), 0 < r ∧ ∀ j, (A *ᵥ c) j + r * ‖A j‖₂ ≤ b j := by -- --- PROOF ---
  have hdeg := interior_eq_empty_iff_forall_ball (HPolytope.ineqs A b).construct
  rw [← Set.not_nonempty_iff_eq_empty] at hdeg
  rw [← not_iff_not, hdeg]
  push Not
  constructor
  · intro h c r hr
    by_contra hall
    push Not at hall
    -- every row holds the ball, so the ball is inside and `c` is a point
    have hball : ∀ x : Vec ℝ n, ‖x‖₂ ≤ r → c + x ∈ (HPolytope.ineqs A b).construct :=
      fun x hx => HPolytope.mem_ineqs_iff.mpr fun j =>
        (aux_ball_subset_iff (A j) c hr.le (b j)).mpr (hall j) x hx
    have hc : c ∈ (HPolytope.ineqs A b).construct := by
      simpa using hball 0 (by rw [norm₂_zero]; exact hr.le)
    obtain ⟨x, hx, hxn⟩ := h c hc r hr
    exact hxn (hball x hx)
  · intro h s _ ε hε
    obtain ⟨j, hj⟩ := h s ε hε
    -- the row `j` cuts the ball: some point of it violates that row
    have hcut : ¬ ∀ x : Vec ℝ n, ‖x‖₂ ≤ ε → A j ⬝ᵥ (s + x) ≤ b j :=
      fun hall => absurd ((aux_ball_subset_iff (A j) s hε.le (b j)).mp hall) (not_le.mpr hj)
    push Not at hcut
    obtain ⟨x, hx, hxb⟩ := hcut
    exact ⟨x, hx, fun hmem => absurd (HPolytope.mem_ineqs_iff.mp hmem j) (not_le.mpr hxb)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
