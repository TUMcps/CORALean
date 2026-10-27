module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.luenbergerUpdate`

The set-propagation observer's Luenberger step, Step 1 of [1, Alg. 2], [1, Thm. 2]: from the
zonotope `⟨ĉ, Ĝ⟩` of the previous state, the gain `Λ`, the stacked measurement `ȳ`, the
process-noise generators `Q` (`n_k ∈ ⟨0, Q⟩`) and the measurement-noise generators `R`
(`v̄ ∈ ⟨0, R⟩`), `c̄ = F ĉ + Λ (ȳ - Γ ĉ)` Eq. 28 of [1, Thm. 2] and
`Ḡ = [(F - Λ Γ) Ĝ, -Λ R, Q]` Eq. 29 of [1, Thm. 2]. `Q` and `R` are matrices of generator
columns, as the zonotopes `⟨0, Q⟩` and `⟨0, R⟩` have no center; `Λ` is any matrix.

## Inputs
* `F` – dynamics matrix
* `Γ` – stacked measurement matrix
* `Λ` – gain matrix
* `Q` – process-noise generators
* `R` – measurement-noise generators
* `y` – stacked output
* `X` – zonotope

## Output
* zonotope after the Luenberger update

## References

* [1] [A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      2023.](../../../../../../references/2023/alanwar-jfi-diffusion-observers.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p nq nr : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.luenbergerUpdate (F : Mat ℝ n n) (Γ : Mat ℝ p n) (Λ : Mat ℝ n p) (Q : Mat ℝ n nq)
    (R : Mat ℝ p nr) (y : Vec ℝ p) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  { h := X.h + nr + nq
    c := F *ᵥ X.c + Λ *ᵥ (y - Γ *ᵥ X.c)                                  -- Eq. 28
    G := Fin.append (Fin.append
      (fun j => (F - Λ * Γ) *ᵥ X.G j)                                      -- (F - Λ Γ) Ĝ
      (fun j i => (-(Λ * R)) i j))                                          -- -Λ R
      (fun j i => Q i j) }                                                  -- Q, Eq. 29

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
