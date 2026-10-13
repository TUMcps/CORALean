import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Shenmaier halfspace sampling

`[1, Alg. 2]`, CORA's `contains_(..., 'sampling:dual')` for ellipsotopes: from samples
`vᵢ` of the circumbody `E_q(H)` and their maximizers `zᵢ = argmax_{‖Hᵀz‖_{q*} ≤ 1} zᵀvᵢ`
(lines 1-2, supplied: a sampler and an optimizer), `r_{Shs,i} = ‖Gᵀzᵢ‖_{p*} + zᵢᵀ(c - d)`
(line 3), their maximum (line 4), then `False` if it exceeds `1` and
`P_S(1 - r_Shs)` (`[1, Thm. 4.2, Eq. 18]`) otherwise. `none` is the listing's `False`. The
dual norm is the operator norm of `z ∘ G`, any norm on the coefficients.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `P_S(ε) = 1 - (1 - (ε / (2 + ε))ⁿ + ϑ)^N`, `[1, Thm. 4.2, Eq. 18]`. -/
noncomputable def shenmaierProb (n N : ℕ) (ϑ ε : ℝ) : ℝ := 1 - (1 - (ε / (2 + ε)) ^ n + ϑ) ^ N

/-- Lines 3-4: `r_Shs = maxᵢ ‖Gᵀzᵢ‖_{p*} + zᵢᵀ(c - d)`. -/
noncomputable def shenmaierHalfspaceValue (G : E →ₗ[ℝ] V) (c d : V) {N : ℕ} (hN : 0 < N)
    (z : Fin N → V →L[ℝ] ℝ) : ℝ :=
  let r : Fin N → ℝ := fun i => ‖(z i).comp (LinearMap.toContinuousLinearMap G)‖ + z i (c - d)
  Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ r


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Alg. 2]`: `none` (non-containment confirmed) or the lower bound `P_Shs`. -/
noncomputable def shenmaierHalfspace (G : E →ₗ[ℝ] V) (c d : V) {N : ℕ} (hN : 0 < N)
    (z : Fin N → V →L[ℝ] ℝ) (ϑ : ℝ) : Option ℝ :=
  let rShs := shenmaierHalfspaceValue G c d hN z
  if rShs > 1 then none else some (shenmaierProb (Module.finrank ℝ V) N ϑ (1 - rShs))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
