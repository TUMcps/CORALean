import Mathlib.Analysis.Calculus.Taylor

/-!
# The Lagrange remainder, bounded

Taylor's theorem with the Lagrange remainder in the form a validated method spends: if
`|g⁽ᴺ⁺¹⁾| ≤ D` between `c` and `x`, the degree-`N` expansion at `c` is off by at most
`D |x - c|ᴺ⁺¹ / (N+1)!`. Mathlib's `taylor_mean_remainder_lagrange_iteratedDeriv` gives the
mean-value point; what is added is reading its within-the-segment derivatives at `c` as the
global `iteratedDeriv`, which smoothness at `c` allows, and the case `x = c`, which it
excludes. Global derivatives keep the statement usable for `log` and `sqrt`, smooth only on
an open half-line.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same at `x = c + y`, the form the case split is easier in. -/
theorem aux_taylor_remainder_abs_le {g : ℝ → ℝ} {N : ℕ} {c y D : ℝ}
    (hg : ∀ ξ ∈ Set.uIcc c (c + y), ContDiffAt ℝ (N + 1) g ξ)
    (hD : ∀ ξ ∈ Set.uIcc c (c + y), |iteratedDeriv (N + 1) g ξ| ≤ D) :
    |g (c + y) - ∑ k ∈ Finset.range (N + 1),
        iteratedDeriv k g c / (k.factorial : ℝ) * y ^ k|
      ≤ D * |y| ^ (N + 1) / ((N + 1).factorial : ℝ) := by -- --- PROOF ---
  rcases eq_or_ne y 0 with rfl | hy
  · -- `y = 0`: only the constant term survives, and it is `g c`
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun k _ => by simp)]
    simp
  have hne : c ≠ c + y := by intro h; apply hy; linarith
  have hf : ContDiffOn ℝ (N + 1) g (Set.uIcc c (c + y)) :=
    fun ξ hξ => (hg ξ hξ).contDiffWithinAt
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf
  have hu : UniqueDiffOn ℝ (Set.uIcc c (c + y)) := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne hne with h | h
    · simp [min_eq_left h.le, max_eq_right h.le, h]
    · simp [min_eq_right h.le, max_eq_left h.le, h])
  have hc : c ∈ Set.uIcc c (c + y) := Set.left_mem_uIcc
  -- the within-the-segment Taylor polynomial is the global one: `g` is smooth at `c`
  have htay : taylorWithinEval g N (Set.uIcc c (c + y)) c (c + y)
      = ∑ k ∈ Finset.range (N + 1), iteratedDeriv k g c / (k.factorial : ℝ) * y ^ k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (k : WithTop ℕ∞) ≤ (N + 1 : ℕ) := by
      have := Finset.mem_range.1 hk
      exact_mod_cast (by omega : k ≤ N + 1)
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hg c hc).of_le (by exact_mod_cast hk')) hc,
      smul_eq_mul, add_sub_cancel_left]
    ring
  rw [← htay, h, abs_div, abs_mul, abs_pow, add_sub_cancel_left]
  rw [abs_of_pos (by positivity : (0:ℝ) < ((N + 1).factorial : ℝ))]
  gcongr
  exact hD ξ (Set.uIoo_subset_uIcc_self hξ)


-- =======================================  MAIN THEOREM  ======================================= --

theorem taylor_remainder_abs_le {g : ℝ → ℝ} {N : ℕ} {c x D : ℝ}
    (hg : ∀ ξ ∈ Set.uIcc c x, ContDiffAt ℝ (N + 1) g ξ)
    (hD : ∀ ξ ∈ Set.uIcc c x, |iteratedDeriv (N + 1) g ξ| ≤ D) :
    |g x - ∑ k ∈ Finset.range (N + 1), iteratedDeriv k g c / (k.factorial : ℝ) * (x - c) ^ k|
      ≤ D * |x - c| ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  have h := aux_taylor_remainder_abs_le (g := g) (N := N) (c := c) (y := x - c) (D := D)
    (by rwa [add_sub_cancel]) (by rwa [add_sub_cancel])
  rwa [add_sub_cancel] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
