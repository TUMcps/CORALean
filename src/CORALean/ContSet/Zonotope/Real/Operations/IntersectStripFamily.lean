module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Zonotope.intersectStripFamily`

The zonotope that [1, Lemma 1] gives for a family of `m` strips `|H_j x - y_j| ≤ r_j`, each of
`p` rows with one radius `r_j`: centre `c + Σ_j λ_j (y_j - H_j c)` and generators
`[(I - Σ_j λ_j H_j) G, λ_1 r_1, …, λ_m r_m]`, the last `m p` being the columns of the `λ_j` scaled
by `r_j`. It is `intersectStrip` at the stacked strip (`intersectStripFamily_eq`), written the way
the paper writes it. The gains `λ_j` are arguments, as in [1] they are a degree of freedom.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 1]: `Z ∩ P₁ ∩ ⋯ ∩ Pₘ` is enclosed by this zonotope, for strips `Pⱼ` of radius `rⱼ`. -/
def Zonotope.intersectStripFamily (H : Fin m → Mat ℝ p n) (r : Fin m → ℝ) (y : Fin m → Vec ℝ p)
    (lam : Fin m → Mat ℝ n p) (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) where
  h := Z.h + m * p
  c := Z.c + ∑ j, lam j *ᵥ (y j - H j *ᵥ Z.c)                  -- eq. 15
  G := Fin.append (fun l => (1 - ∑ j, lam j * H j) *ᵥ Z.G l)    -- eq. 16, old generators
    fun q => r (finProdFinEquiv.symm q).1 •                      -- eq. 16, λⱼ rⱼ
      fun a => lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
