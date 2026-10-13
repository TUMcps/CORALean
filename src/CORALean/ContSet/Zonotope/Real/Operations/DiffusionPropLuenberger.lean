module

public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerGain
public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerUpdate

@[expose] public section

/-!
# `Zonotope.diffusionPropLuenberger`

The Luenberger update, Step 1 of [1, Alg. 2], at every node `i` from the zonotope `Ẑⁱ = ⟨ĉⁱ, Ĝⁱ⟩`
of the previous instant: the gain `Λ` of minimal `‖Ḡ‖_F` (`luenbergerGain`, Eq. 31 of [1, Prop.
2]) and the zonotope of [1, Thm. 2], `c̄ = Fĉ + Λ(ȳ - Γĉ)`, `Ḡ = [(F - ΛΓ)Ĝ, -ΛR, Q]`, Eqs. 28-29
(`luenbergerUpdate`). `Γⁱ` and `ȳⁱ` are the stacked measurement matrix and output of the `m_i`
neighbours, `Rⁱ = diag rⁱ` the stacked noise radii.
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

variable {n nq N : ℕ} {p : Fin N → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.diffusionPropLuenberger (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (Zh : Fin N → Zonotope (Vec ℝ n)) :
    Fin N → Zonotope (Vec ℝ n) :=
  fun i =>
    let R : Mat ℝ (p i) (p i) := Matrix.diagonal (r i)                      -- Rⁱ = diag rⁱ
    let Λ : Mat ℝ n (p i) :=                                                -- Λ = argmin ‖Ḡ‖_F
      Zonotope.luenbergerGain F (Γ i) R (Zh i)                              -- Eq. 31
    Zonotope.luenbergerUpdate F (Γ i) Λ Q R (yb i) (Zh i)                    -- c̄ and Ḡ, Eqs. 28-29

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
