import CORALean.ContSet.HPolytope.Real.Definitions.ExtendedRow
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Naive halfspace sampling's value

`[1, Eq. 12]`: for sampled facets `(λ_{jᵢ}, b_{jᵢ})` of `Z(H) = {Λ x ≤ b}`,
`r_hs = max_i ‖G'ᵀ λ_{jᵢ}‖_{p*} / |b_{jᵢ}|` with `G' = [G, c - d]`, the norm of each
row being the operator norm of `HPolytope.extendedRow`.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ENNReal

variable {n s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `r_hs = maxᵢ ‖G'ᵀ λ_{jᵢ}‖_{p*} / |b_{jᵢ}|` over `N` sampled facets `jᵢ`. -/
noncomputable def HPolytope.naiveHalfspaceValue (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (G : E →ₗ[ℝ] Vec ℝ n) (c d : Vec ℝ n) (Λ : Mat ℝ s n) (b : Vec ℝ s) {N : ℕ} (hN : 0 < N)
    (j : Fin N → Fin s) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ fun i =>
    ‖HPolytope.extendedRow p G c d Λ (j i)‖ / |b (j i)|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
