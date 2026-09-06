import CORALean.NN.Layers.PolyConvergence
import CORALean.NN.Layers.PolyDerivBound

/-!
# Refinement by order converges, and what the fit must guarantee

Weierstrass gives a polynomial within `ε` of `σ` on the box, so the half-range
`PolyConvergence` converges to is itself driven to zero by raising the order.
Samples take the error down to the half-range, order takes the half-range to
zero, and the enclosure converges to the exact image — refinement's point [1].

It does not close as one limit, and the reason is the result. `ofSampling` also
needs `M`, a bound on `|σ' - p'|`, and uniform convergence of `pₙ` says nothing
about `pₙ'` — `M` may blow up with the degree, and then the padding
`M · (u - l) / N` does not vanish at a fixed `N`. So the statement quantifies
jointly: for every `ε` an order *and* a sample count under it, `N` free to
depend on the degree. That is what refinement does anyway, and a limit at a
fixed `N` would instead need `pₙ' → σ'` uniformly, which no `poly_method`
promises and Weierstrass does not give.

`σ'` is asked to be bounded on the box, which sigmoid and tanh satisfy globally,
and `polyDerivDiff` supplies the rest of `M` out of the fit itself.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- Mathlib's polynomials read as `evalPoly` does: coefficients indexed by
degree, up to the natural degree. -/
theorem evalPoly_coeff (p : Polynomial ℝ) (t : ℝ) :
    evalPoly (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)) t = Polynomial.eval t p := by
  rw [Polynomial.eval_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (p.natDegree + 1)

/-- Weierstrass in the form a fit is handed in: an order and coefficients whose
polynomial is within `ε` of `σ` everywhere on the box. -/
theorem exists_evalPoly_near {σ : ℝ → ℝ} {l u ε : ℝ} (hcont : ContinuousOn σ (Set.Icc l u))
    (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ), ∀ x, l ≤ x → x ≤ u → |σ x - evalPoly c x| ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn l u σ hcont ε hε
  refine ⟨p.natDegree, fun i => p.coeff (i : ℕ), fun x hx hx' => ?_⟩
  rw [evalPoly_coeff p x, abs_sub_comm]
  exact le_of_lt (hp x ⟨hx, hx'⟩)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Refinement converges: some order and sample count put `ofSampling`'s error
under any `ε`. `N` may depend on the order, which is where `M`'s blow-up goes. -/
theorem exists_fit_samplingError_lt {σ σ' : ℝ → ℝ} {l u Mσ ε : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, l ≤ x → x ≤ u → |σ' x| ≤ Mσ)
    (hlu : l ≤ u) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ) (M : ℝ) (N : ℕ), 0 < N
      ∧ (∀ x, l ≤ x → x ≤ u → |σ' x - evalPolyDeriv c x| ≤ M)
      ∧ samplingError (fun x => σ x - evalPoly c x) M l u N < ε := by
  have hcont : ContinuousOn σ (Set.Icc l u) :=
    fun x _ => ((hd x).continuousAt).continuousWithinAt
  -- a quarter of the budget goes on the fit, which fixes the order and with it `M`
  obtain ⟨n, c, hfit⟩ := exists_evalPoly_near hcont (show (0:ℝ) < ε / 4 by linarith)
  refine ⟨n, c, polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u), ?_⟩
  have hMbound : ∀ x, l ≤ x → x ≤ u →
      |σ' x - evalPolyDeriv c x|
        ≤ polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u) := by
    intro x hx hx'
    obtain ⟨h₁, h₂⟩ := abs_le.mp (hσ x hx hx')
    exact abs_sub_evalPolyDeriv_le h₁ h₂ hx hx'
  have hM0 : 0 ≤ polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u) :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  set M := polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u) with hMdef
  -- and half of it on the padding, which only now can be asked to be small
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max 1 (2 * (M * (u - l)) / ε))
  have hmax1 : (1:ℝ) ≤ max 1 (2 * (M * (u - l)) / ε) := le_max_left _ _
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by linarith) hNgt
  have hN : 0 < N := Nat.cast_pos.mp hNpos
  have hpad : M * ((u - l) / N) < ε / 2 := by
    have h2 : 2 * (M * (u - l)) / ε < N := lt_of_le_of_lt (le_max_right _ _) hNgt
    rw [div_lt_iff₀ hε] at h2
    rw [← mul_div_assoc, div_lt_iff₀ hNpos]
    linarith
  -- the samples lie in the box, so the fit's own bound caps the sampled range
  have hgb : ∀ i : Fin (N + 1),
      |σ (sampleGrid l u N i) - evalPoly c (sampleGrid l u N i)| ≤ ε / 4 := by
    intro i
    obtain ⟨ha, hb⟩ := sampleGrid_mem_Icc hN hlu i
    exact hfit _ ha hb
  have hsup : sampleSup (fun x => σ x - evalPoly c x) l u N ≤ ε / 4 :=
    Finset.sup'_le _ _ fun i _ => (abs_le.mp (hgb i)).2
  have hinf : -(ε / 4) ≤ sampleInf (fun x => σ x - evalPoly c x) l u N :=
    Finset.le_inf' _ _ fun i _ => (abs_le.mp (hgb i)).1
  refine ⟨N, hN, hMbound, ?_⟩
  show (sampleSup (fun x => σ x - evalPoly c x) l u N
    - sampleInf (fun x => σ x - evalPoly c x) l u N) / 2 + M * ((u - l) / N) < ε
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
