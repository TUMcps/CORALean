import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStrip
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `ConZonotope.intersectStripFamily`

The constrained zonotope that [1, Lemma 2] gives for the intersection of `ĉ + Ĝ ξ` with `m`
strips `|H_j x - y_j| ≤ r_j`, each of `p` rows with one radius `r_j`: the centre and generators of
the zonotopic case ([1, Lemma 1]), `m p` new factors `ν`, and one equality row per strip row,
`H_j Ĝ ξ - r_j ν_jk = y_jk - (H_j ĉ)_k`, below the old constraints, which keep acting on the old
factors. It is `intersectStrip` at the stacked strip (`intersectStripFamily_exact`). The gains
`λ_j` are arguments, as in [1] they are a degree of freedom.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 2]: `cZ ∩ P₁ ∩ ⋯ ∩ Pₘ`, exactly, for strips `Pⱼ` of radius `rⱼ`. -/
def ConZonotope.intersectStripFamily (cZ : ConZonotope (Vec ℝ n)) (H : Fin m → Mat ℝ p n)
    (r : Fin m → ℝ) (y : Fin m → Vec ℝ p) (lam : Fin m → Mat ℝ n p) : ConZonotope (Vec ℝ n) where
  h := cZ.h + m * p
  c := cZ.c + ∑ j, lam j *ᵥ (y j - H j *ᵥ cZ.c)                  -- eq. 21
  G := Fin.append (fun l => (1 - ∑ j, lam j * H j) *ᵥ cZ.G l)    -- eq. 22
    fun q => r (finProdFinEquiv.symm q).1 •
      fun a => lam (finProdFinEquiv.symm q).1 a (finProdFinEquiv.symm q).2
  P := (cZ.P.comap (blockLeft cZ.h (m * p))).intersection        -- eqs. 23-24
    (HPolytope.eqs
      (cZ.stripMat (Matrix.of fun q a => H (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 a)
        fun q => r (finProdFinEquiv.symm q).1)
      fun q => y (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
        - (H (finProdFinEquiv.symm q).1 *ᵥ cZ.c) (finProdFinEquiv.symm q).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
