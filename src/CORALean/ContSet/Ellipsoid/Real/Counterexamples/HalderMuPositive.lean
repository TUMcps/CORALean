module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderMu

@[expose] public section

/-!
# Halder's Corollary 1 fails: the coefficients are not positive

[1, Cor. 1] claims every coefficient `µᵣ`, `1 ≤ r ≤ d − 1`, of [1, Eq. 23] is positive,
so that the polynomial (24) has a single sign change. For `d = 3` and `λ = (1, 1, 10)`,
`e₁ = 21/10` and `e₂ = 6/5` give `µ₂ = (3 − 2) e₂ − (2 − 1) e₁ = −9/10 < 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the coefficients `µ` are not all positive

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_e1 :
    Ellipsoid.halderElemSymm (fun i : Fin 3 => ((![1, 1, 10] : Fin 3 → ℝ) i)⁻¹) 1
      = 21 / 10 := by
  unfold Ellipsoid.halderElemSymm
  rw [show (Finset.powersetCard 1 (Finset.univ : Finset (Fin 3))) = {{0}, {1}, {2}} from by decide]
  simp
  norm_num

theorem Ellipsoid.aux_e2 : -- --- CONCL ---
    Ellipsoid.halderElemSymm (fun i : Fin 3 => ((![1, 1, 10] : Fin 3 → ℝ) i)⁻¹) 2
      = 6 / 5 := by -- --- PROOF ---
  unfold Ellipsoid.halderElemSymm
  rw [show (Finset.powersetCard 2 (Finset.univ : Finset (Fin 3))) = {{0, 1}, {0, 2}, {1, 2}}
    from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 1] is false: `µ₂ < 0` for `λ = (1, 1, 10)`. -/
theorem Ellipsoid.not_halderMu_positive : -- --- CONCL ---
    ¬ ∀ (d : ℕ) (lam : Fin d → ℝ), (∀ i, 0 < lam i) → ∀ r : ℕ, 1 ≤ r → r + 1 ≤ d →
      0 < Ellipsoid.halderMu lam r := by -- --- PROOF ---
  intro h
  have hpos : ∀ i, 0 < (![1, 1, 10] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have := h 3 ![1, 1, 10] hpos 2 (by norm_num) (by norm_num)
  -- evaluate the coefficient at `λ = (1, 1, 10)`
  unfold Ellipsoid.halderMu at this
  simp only [Fintype.card_fin, one_div] at this
  norm_num [Ellipsoid.aux_e1, Ellipsoid.aux_e2] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
