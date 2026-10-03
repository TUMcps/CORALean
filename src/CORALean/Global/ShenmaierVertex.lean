import CORALean.Global.ShenmaierHalfspace
import CORALean.Global.CoeffNorm

/-!
# Shenmaier vertex sampling

`[1, Alg. 3]`, CORA's `contains_(..., 'sampling:primal')` for ellipsotopes: from samples
`vᵢ` of `B_{p*}` and the points `zᵢ = argmax_{z ∈ B_p} zᵀvᵢ` (lines 1-2, supplied; the
closed form is `[1, Eq. 21]`), `r_{Svs,i} = ‖G zᵢ + c - d‖_{E_q(H)}` (line 3), their maximum
(line 4), then `False` above `1` and `P_S(1 - r_Svs)` at `ϑ = 0` otherwise; `none` is
`False`. Any norms on the coefficients.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E₁ E₂ V : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [AddCommGroup V] [Module ℝ V]

/-- Lines 3-4: `r_Svs = maxᵢ ‖G zᵢ + c - d‖_{E_q(H)}`. -/
noncomputable def shenmaierVertexValue (G : E₁ →ₗ[ℝ] V) (c : V) (H : E₂ →ₗ[ℝ] V) (d : V)
    {N : ℕ} (hN : 0 < N) (z : Fin N → E₁) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ fun i => coeffNorm H (G (z i) + c - d)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Alg. 3]`: `none` (non-containment confirmed) or the lower bound `P_Svs`. -/
noncomputable def shenmaierVertex (G : E₁ →ₗ[ℝ] V) (c : V) (H : E₂ →ₗ[ℝ] V) (d : V) (n : ℕ)
    {N : ℕ} (hN : 0 < N) (z : Fin N → E₁) : Option ℝ :=
  let rSvs := shenmaierVertexValue G c H d hN z
  if rSvs > 1 then none else some (shenmaierProb n N 0 (1 - rSvs))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
