import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.HalderMu

/-!
# Halder's Lemma 2 fails: the coefficients are not increasing

[1, Lemma 2] claims `µ₁ < µ₂ < ⋯ < µ_{d−1}` for the coefficients of [1, Eq. 23]. Its proof
writes `µ₂ − µ₁ = (d − 2)(e₂ + e₁)`, but by [1, Eq. 23] it is `(d − 2) e₂ − d e₁`. For
`d = 3` and `λ = (1, 1, 10)`, `e₁ = 21/10` and `e₂ = 6/5`, so `µ₁ = 21/5` and
`µ₂ = −9/10`: the sequence falls.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


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

theorem Ellipsoid.aux_e2 :
    Ellipsoid.halderElemSymm (fun i : Fin 3 => ((![1, 1, 10] : Fin 3 → ℝ) i)⁻¹) 2
      = 6 / 5 := by -- --- PROOF ---
  unfold Ellipsoid.halderElemSymm
  rw [show (Finset.powersetCard 2 (Finset.univ : Finset (Fin 3))) = {{0, 1}, {0, 2}, {1, 2}}
    from by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2] is false: `µ₂ < µ₁` for `λ = (1, 1, 10)`. -/
theorem Ellipsoid.not_halderMu_strictly_increasing :
    ¬ ∀ (d : ℕ) (lam : Fin d → ℝ), (∀ i, 0 < lam i) → ∀ r : ℕ, 1 ≤ r → r + 2 ≤ d →
      Ellipsoid.halderMu lam r < Ellipsoid.halderMu lam (r + 1) := by -- --- PROOF ---
  intro h
  have hpos : ∀ i, 0 < (![1, 1, 10] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have := h 3 ![1, 1, 10] hpos 1 le_rfl (by norm_num)
  -- evaluate both coefficients at `λ = (1, 1, 10)`
  unfold Ellipsoid.halderMu at this
  simp only [Fintype.card_fin, one_div] at this
  norm_num [Ellipsoid.aux_e1, Ellipsoid.aux_e2] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
