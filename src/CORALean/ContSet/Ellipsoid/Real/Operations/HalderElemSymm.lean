module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# Elementary symmetric polynomials of the reciprocal eigenvalues

The `eᵣ = eᵣ(1/λ₁, …, 1/λ_d)` of [1, Eq. 23], the `r`-th elementary symmetric polynomial of
the reciprocals: the sum over the `r`-element subsets of the product of their entries, with
`e₀ = 1` by convention. They are the coefficients through which the polynomial form of
[1, Eq. 18] is read in the proof of [1, Thm. 2].

## Inputs
* `x` – entries
* `r` – subset size

## Output
* sum over `r`-element subsets of the product of the entries

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC), 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eᵣ(x)`, the sum over `r`-element subsets of the product of the entries ([1, Eq. 23]). -/
noncomputable def Ellipsoid.halderElemSymm (x : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ s ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ s, x i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
