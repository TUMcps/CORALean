module

public import CORALean.ContSet.ProbZonotope.Float.Theorems.MaxLe
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GaussPdfLeMaxIff

@[expose] public section

/-!
# The float `max` bounds the density outside the `m`-sigma ellipsoid

For every symmetric `Σ` of the covariance interval and every mean `c`, when the float `max`
returns `v`: the density of `N(c, Σ)` at every `x` on or outside the `m`-sigma ellipsoid,
`m² ≤ (x - c)ᵀ Σ⁻¹ (x - c)`, is at most `v`. `Real.ProbZonotope.gaussPdf_le_max_iff` puts the
density under the real `max`, and `max_le` the real `max` under `v`; an upper bound, not attained.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open WithLp Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.gaussPdf_le_max (P : ProbZonotope 𝕋 n) (m : 𝕋) (p k : ℕ) {v : 𝕋}
    (hv : P.max m p k = some v) {S : Mat ℝ n n} (hS : S ∈ P.cov.construct)
    (hSh : S.IsHermitian) (c : Vec ℝ n) (x : EuclideanSpace ℝ (Fin n))
    (hx : toReal m ^ 2 ≤ (ofLp x - c) ⬝ᵥ S⁻¹ *ᵥ (ofLp x - c)) : -- --- STMT ---
    Real.gaussPdf c S x ≤ toReal v := by -- --- PROOF ---
  obtain ⟨hdet, hle⟩ := P.max_le m p k hv ⟨0, 0, Fin.elim0⟩ hS hSh
  exact le_trans
    ((Real.ProbZonotope.gaussPdf_le_max_iff ⟨⟨0, 0, Fin.elim0⟩, S⟩ hdet c x (toReal m)).mpr hx)
    hle

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
