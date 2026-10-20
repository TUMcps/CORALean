module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Real.Operations.StripGain

@[expose] public section

/-!
# `Zonotope.diffusionStripMeasurement`

The measurement update, Step 1 of [1, Alg. 1], at every node `i` from its predicted zonotope `Ẑⁱ =
⟨ĉⁱ, Ĝⁱ⟩`: the gain `Λ` of minimal `‖Ḡ‖_F` (`stripGain`, [1, Eq. 38]) and the zonotope of [1,
Lemma 1], Eq. 12-13, `c̄ = ĉ + Λ(ȳ - Γĉ)`, `Ḡ = [(I - ΛΓ)Ĝ, ΛR]` (`intersectStrip`, which runs the
two lines at `Λ`). `Γⁱ` and `ȳⁱ` are the stacked measurement matrix and output of the `m_i`
neighbours, `Rⁱ = diag rⁱ` the stacked noise radii [1].

## Inputs
* `Γ` – stacked measurement matrices
* `r` – noise radii
* `yb` – outputs
* `Zh` – predicted zonotope of each node

## Output
* measurement-updated zonotope of each node

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ} {p : Fin N → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.diffusionStripMeasurement (Γ : ∀ i, Mat ℝ (p i) n)
    (r yb : ∀ i, Vec ℝ (p i)) (Zh : Fin N → Zonotope (Vec ℝ n)) : Fin N → Zonotope (Vec ℝ n) :=
  fun i =>
    let R : Mat ℝ (p i) (p i) := Matrix.diagonal (r i)                     -- Rⁱ = diag rⁱ
    let Λ : Mat ℝ n (p i) :=                                                -- Λ = argmin ‖Ḡ‖_F
      Zonotope.stripGain (Γ i) R (Zh i)                                     -- Eq. 38
    (Zh i).intersectStrip (Γ i) (r i) (yb i) Λ                      -- c̄ and Ḡ, Eqs. 12-13

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
