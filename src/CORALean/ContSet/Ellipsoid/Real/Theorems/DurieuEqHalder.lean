module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# The Durieu-Walter-Polyak parameterization is Halder's at a change of variable

[1, Eq. 13]: Durieu, Walter and Polyak's `Q(α) = ∑ₖ α_k⁻¹ Qₖ` of [1, Eq. 10] at two
ellipsoids and `α₂ = 1 − α₁` is `(1 + 1/β) Q₁ + (1 + β) Q₂` of [1, Eq. 11] at
`β = α₁/(1 − α₁)`, since `1 + 1/β = 1/α₁` and `1 + β = 1/(1 − α₁)`.

## Inputs
* `Q₁` – first shape matrix
* `Q₂` – second shape matrix
* `α₁` – weight

## Hypotheses
* `h₀` – `0 < α₁`
* `h₁` – `α₁ < 1`

## Conclusion
* the `K = 2` sum equals Halder's sum at `β = α₁ / (1 − α₁)`

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

variable {n : Type*}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13]: [1, Eq. 10] at `K = 2` is [1, Eq. 11] at `β = α₁ / (1 − α₁)`. -/
theorem Ellipsoid.durieu_eq_halder {Q₁ Q₂ : Matrix n n ℝ} {α₁ : ℝ} (h₀ : 0 < α₁)
    (h₁ : α₁ < 1) : -- --- CONCL ---
    α₁⁻¹ • Q₁ + (1 - α₁)⁻¹ • Q₂
      = (1 + 1 / (α₁ / (1 - α₁))) • Q₁ + (1 + α₁ / (1 - α₁)) • Q₂ := by -- --- PROOF ---
  have h : 1 - α₁ ≠ 0 := (sub_pos.2 h₁).ne'
  -- compare the coefficients of `Q₁` and of `Q₂`
  congr 2
  · field_simp; ring
  · field_simp; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
