module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionPropLuenberger
public import CORALean.ContSet.Zonotope.Real.Theorems.LuenbergerUpdateOuter

@[expose] public section

/-!
# The Luenberger update of the diffusion observer holds the next state

[1, Alg. 2] Step 1, [1, Thm. 2]: a state `x` in the zonotope of node `i` whose output meets the
strips `|Γⁱ x - ȳⁱ| ≤ rⁱ` goes on to `F x + Q β`, `|β| ≤ 1`, in the zonotope of the update. The
measurement noise `v̄ = Rγ` is read off the strips, `γⱼ = (ȳ - Γx)ⱼ / rⱼ`, so the innovation `ȳ -
Γx - v̄` vanishes and the term `Λ (⋯)` of Eq. 27 of [1, Thm. 2] drops out.
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the strip residual as noise coefficients of the diagonal `R = diag r`
theorem Zonotope.aux_stripCoeff {k : ℕ} (a r : Vec ℝ k) (h : ∀ j, |a j| ≤ r j) :
    ∃ γ : Vec ℝ k, (∀ j, |γ j| ≤ 1) ∧
      Matrix.diagonal r *ᵥ γ = a := by -- --- PROOF ---
  refine ⟨fun j => a j / r j, fun j => ?_, ?_⟩
  · by_cases h0 : r j = 0
    · simp [h0]
    · have hr : 0 < r j := lt_of_le_of_ne (le_trans (abs_nonneg _) (h j)) (Ne.symm h0)
      rw [abs_div, abs_of_pos hr]
      exact (div_le_one hr).mpr (h j)
  · ext j
    simp only [mulVec_diagonal]
    by_cases h0 : r j = 0
    · have : a j = 0 := abs_nonpos_iff.mp (h0 ▸ h j)
      simp [h0, this]
    · field_simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionPropLuenberger_outer (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (Zh : Fin N → Zonotope (Vec ℝ n))
    (x : Vec ℝ n) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1) (i : Fin N) (hx : x ∈ (Zh i).construct)
    (hy : ∀ j, |(Γ i *ᵥ x - yb i) j| ≤ r i j) :
    F *ᵥ x + Q *ᵥ β ∈
      (Zonotope.diffusionPropLuenberger F Q Γ r yb Zh i).construct := by -- --- PROOF ---
  obtain ⟨γ, hγ, hRγ⟩ := Zonotope.aux_stripCoeff (yb i - Γ i *ᵥ x) (r i) (fun j => by
    rw [← abs_neg, Pi.sub_apply]
    simpa using hy j)
  have := Zonotope.luenbergerUpdate_outer F (Γ i)
    (Zonotope.luenbergerGain F (Γ i) (Matrix.diagonal (r i)) (Zh i)) Q (Matrix.diagonal (r i))
    (yb i) (Zh i) x hx β hβ γ hγ
  rw [hRγ, sub_self, mulVec_zero, add_zero] at this
  unfold Zonotope.diffusionPropLuenberger
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
