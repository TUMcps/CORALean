import CORALean.ContDynamics.NonlinearSys.EstimateGain

/-!
# What `estimateGain`'s bisection buys

The soundness of line 16 of [1, Alg. 2] as written here: the gain reported sits
between a `φ⁽¹⁾` whose eq. (56) left-hand side is still under the right-hand
side and one already over it, and those two are `2^{-fuel}` apart. Halving a
bracket is all the bisection does, and this is exactly what it gets.

It is not a root: eq. (56)'s left-hand side is not shown continuous here, so
nothing says a crossing point exists. What the theorem gives is the bracket,
which is what a caller can act on and all a float layer could ever check.

The two hypotheses are the starting bracket, `φ⁽¹⁾ = 0` under the target and
`φ⁽¹⁾ = 1` over it. A gain is a ratio of two widths, so that is where the
answer lies whenever there is one; where there is not, the search still returns
a value in `[0,1]` and the theorem simply does not apply.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each halving keeps a passing end and a failing end and halves what lies
between them. -/
theorem aux_estimateGainSearch_bracket (le : ℝ → ℝ → Bool) (g : ℝ → ℝ) (target : ℝ) :
    ∀ (fuel : ℕ) (lo hi : ℝ), lo ≤ hi → le (g lo) target = true → le (g hi) target = false →
      ∃ a b : ℝ, le (g a) target = true ∧ le (g b) target = false ∧
        a ≤ estimateGainSearch le g target lo hi fuel ∧
        estimateGainSearch le g target lo hi fuel ≤ b ∧
        b - a = (hi - lo) / 2 ^ fuel := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hlehi hlo hhi
    rw [show estimateGainSearch le g target lo hi 0 = (lo + hi) / 2 from rfl]
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by norm_num⟩
  | succ k ih =>
    intro lo hi hlehi hlo hhi
    rw [show estimateGainSearch le g target lo hi (k + 1)
      = if le (g ((lo + hi) / 2)) target then estimateGainSearch le g target ((lo + hi) / 2) hi k
        else estimateGainSearch le g target lo ((lo + hi) / 2) k from rfl]
    split
    -- the midpoint still passes, so it becomes the new passing end
    · rename_i hc
      obtain ⟨a, b, ha, hb, h1, h2, h3⟩ := ih ((lo + hi) / 2) hi (by linarith) hc hhi
      exact ⟨a, b, ha, hb, h1, h2, by rw [h3, pow_succ]; ring⟩
    · rename_i hc
      obtain ⟨a, b, ha, hb, h1, h2, h3⟩ :=
        ih lo ((lo + hi) / 2) (by linarith) hlo (by simpa using hc)
      exact ⟨a, b, ha, hb, h1, h2, by rw [h3, pow_succ]; ring⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] line 16: the gain reported is bracketed to within `2^{-fuel}`
between a passing and a failing value of eq. (56). -/
theorem estimateGain_bracket {le : ℝ → ℝ → Bool} (ζδ lam rabs1 rabsOpt : ℝ)
    (scalings fuel : ℕ)
    (hlo : le (∏ j ∈ Finset.range scalings, interpGain ζδ 0 j)
      (lam * rabsOpt / rabs1) = true)
    (hhi : le (∏ j ∈ Finset.range scalings, interpGain ζδ 1 j)
      (lam * rabsOpt / rabs1) = false) :
    ∃ a b : ℝ,
      le (∏ j ∈ Finset.range scalings, interpGain ζδ a j) (lam * rabsOpt / rabs1) = true ∧
      le (∏ j ∈ Finset.range scalings, interpGain ζδ b j) (lam * rabsOpt / rabs1) = false ∧
      a ≤ estimateGain le ζδ lam rabs1 rabsOpt scalings fuel ∧
      estimateGain le ζδ lam rabs1 rabsOpt scalings fuel ≤ b ∧
      b - a = 1 / 2 ^ fuel := by
  obtain ⟨a, b, ha, hb, h1, h2, h3⟩ := aux_estimateGainSearch_bracket le
    (fun φ1 => ∏ j ∈ Finset.range scalings, interpGain ζδ φ1 j) (lam * rabsOpt / rabs1)
    fuel 0 1 (by norm_num) hlo hhi
  exact ⟨a, b, ha, hb, h1, h2, by rw [h3]; norm_num⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
