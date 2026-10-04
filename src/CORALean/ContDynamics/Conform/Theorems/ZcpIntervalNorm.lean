import CORALean.ContDynamics.Conform.Theorems.ZcpSetEq
import CORALean.ContDynamics.Conform.Theorems.ImageTemplateZono
import CORALean.ContDynamics.Conform.Theorems.IntervalNormSmul

/-!
# The interval norm of a rotated prediction set is linear in the stretch factors

[1, Lemma 4]: `R Y_ZCP(x) = ⟨R f(x), R D̄(x) G_u diag(α)⟩` by [1, Lemma 3], and its interval
norm `1ᵀ|R D̄(x) G_u diag(α)|1` is `1ᵀ|R D̄(x) G_u| α` for `α ≥ 0` (17). The norm is that of the
generator matrix the set is given by, as [1, Def. 2] defines it.

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal
      Prediction: Zonotope-Based Uncertainty Quantification for Regression and
      Classification Tasks". Journal of Machine Learning Research, 26(294):1-37, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ} {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4]: `R Y_ZCP(x)` is `⟨R f(x), R D̄ G_u diag(α)⟩`, of interval norm
`1ᵀ|R D̄ G_u| α`. -/
theorem Conform.intervalNorm_zcpSet {nr : ℕ} (R : Mat ℝ nr ny) (fx : Vec ℝ ny) (D : Mat ℝ ny nu)
    (Gu : ι → Vec ℝ nu) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) :
    (fun y => R *ᵥ y) '' Conform.zcpSet fx D Gu α
        = Conform.templateZono (R *ᵥ fx) (fun j => (R * D) *ᵥ Gu j) α ∧
      Conform.intervalNorm (fun _ => 1) (fun j => α j • (R * D) *ᵥ Gu j)
        = ∑ j, (∑ a, |((R * D) *ᵥ Gu j) a|) * α j := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · rw [Conform.zcpSet_eq, Conform.image_templateZono]
    simp only [mulVec_mulVec]
  · rw [Conform.intervalNorm_smul _ _ _ hα]
    simp only [one_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
