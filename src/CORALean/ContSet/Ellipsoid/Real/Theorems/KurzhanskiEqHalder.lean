module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# The Kurzhanski parameterization is Halder's at a change of variable

[1, Eq. 12]: Kurzhanski's `Q(ℓ) = (∑ₖ √(ℓᵀQₖℓ)) ∑ₖ Qₖ/√(ℓᵀQₖℓ)` of [1, Eq. 9] at two
ellipsoids is `(1 + 1/β) Q₁ + (1 + β) Q₂` of [1, Eq. 11] at `β = √(ℓᵀQ₁ℓ / ℓᵀQ₂ℓ)`: writing
`a = √(ℓᵀQ₁ℓ)` and `b = √(ℓᵀQ₂ℓ)`, `(a + b)(Q₁/a + Q₂/b) = (1 + b/a) Q₁ + (1 + a/b) Q₂`.

## Inputs
* `Q₁` – first shape matrix
* `Q₂` – second shape matrix
* `l` – direction

## Hypotheses
* `h₁` – `0 < lᵀ Q₁ l`
* `h₂` – `0 < lᵀ Q₂ l`

## Conclusion
* the Kurzhanski shape equals Halder's at `β = √(lᵀ Q₁ l / lᵀ Q₂ l)`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12]: [1, Eq. 9] at `K = 2` is [1, Eq. 11] at `β = √(ℓᵀQ₁ℓ / ℓᵀQ₂ℓ)`. -/
theorem Ellipsoid.kurzhanski_eq_halder {Q₁ Q₂ : Matrix n n ℝ} {l : n → ℝ}
    (h₁ : 0 < l ⬝ᵥ Q₁ *ᵥ l) (h₂ : 0 < l ⬝ᵥ Q₂ *ᵥ l) : -- --- CONCL ---
    (Real.sqrt (l ⬝ᵥ Q₁ *ᵥ l) + Real.sqrt (l ⬝ᵥ Q₂ *ᵥ l)) •
        ((Real.sqrt (l ⬝ᵥ Q₁ *ᵥ l))⁻¹ • Q₁ + (Real.sqrt (l ⬝ᵥ Q₂ *ᵥ l))⁻¹ • Q₂)
      = (1 + 1 / Real.sqrt (l ⬝ᵥ Q₁ *ᵥ l / (l ⬝ᵥ Q₂ *ᵥ l))) • Q₁
        + (1 + Real.sqrt (l ⬝ᵥ Q₁ *ᵥ l / (l ⬝ᵥ Q₂ *ᵥ l))) • Q₂ := by -- --- PROOF ---
  have ha : 0 < Real.sqrt (l ⬝ᵥ Q₁ *ᵥ l) := Real.sqrt_pos.2 h₁
  have hb : 0 < Real.sqrt (l ⬝ᵥ Q₂ *ᵥ l) := Real.sqrt_pos.2 h₂
  rw [Real.sqrt_div h₁.le]
  set a := Real.sqrt (l ⬝ᵥ Q₁ *ᵥ l)
  set b := Real.sqrt (l ⬝ᵥ Q₂ *ᵥ l)
  -- the two coefficients agree after clearing `a` and `b`
  rw [smul_add, smul_smul, smul_smul]
  congr 2
  · field_simp
  · field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
