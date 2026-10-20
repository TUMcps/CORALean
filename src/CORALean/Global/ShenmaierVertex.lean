module

public import CORALean.Global.ShenmaierHalfspace
public import CORALean.Global.CoeffNorm

@[expose] public section

/-!
# Shenmaier vertex sampling

`[1, Alg. 3]`, CORA's `contains_(..., 'sampling:primal')` for ellipsotopes: from samples
`vᵢ` of `B_{p*}` and the points `zᵢ = argmax_{z ∈ B_p} zᵀvᵢ` (lines 1-2, supplied; the
closed form is `[1, Eq. 21]`), `r_{Svs,i} = ‖G zᵢ + c - d‖_{E_q(H)}` (line 3), their maximum
(line 4), then `False` above `1` and `P_S(1 - r_Svs)` at `ϑ = 0` otherwise; `none` is
`False`. Any norms on the coefficients.

## Inputs
* `G` – generator map of the inner ellipsotope
* `c` – center of the inner ellipsotope
* `H` – generator map of the outer ellipsotope
* `d` – center of the outer ellipsotope
* `n` – dimension
* `N` – number of samples
* `z` – unit-ball points of the samples

## Hypotheses
* `hN` – there is at least one sample

## Output
* none when containment is refuted, otherwise the probability bound

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
  -- 3. `r_Svs,i ← ‖G zᵢ + c − d‖_{E_q(H)}` and 4. `r_Svs ← maxᵢ r_Svs,i`; lines 1-2 are `z`
  let r_Svs := shenmaierVertexValue G c H d hN z
  -- 5. `if r_Svs > 1 then return False`
  if r_Svs > 1 then none
  else
    -- 8. `P_Svs ← P_S(1 − r_Svs)`, with `ϑ` set to 0
    let P_Svs := shenmaierProb n N 0 (1 - r_Svs)
    -- 9. `return P_Svs`
    some P_Svs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
