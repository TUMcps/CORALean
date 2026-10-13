module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionTimeUpdate
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The time update of the diffusion observers encloses the next state

[1, Alg. 1] Step 3, [1, Def. 2], Eq. 9: if `x ∈ ⟨ć, G̃⟩` and `n ∈ ⟨0, Q⟩`, then `F x + n` is in
`⟨F ć, [F G̃, Q]⟩`. The coefficients of `x` and of the noise are stacked, `(F G̃) α + Q β`.

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

variable {n nq : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionTimeUpdate_outer (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Zt : Zonotope (Vec ℝ n)) (x : Vec ℝ n) (hx : x ∈ Zt.construct) (β : Vec ℝ nq)
    (hβ : ∀ j, |β j| ≤ 1) :
    F *ᵥ x + Q *ᵥ β ∈ (Zonotope.diffusionTimeUpdate F Q Zt).construct := by -- --- PROOF ---
  obtain ⟨α, hα, rfl⟩ := hx
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨Fin.append α β, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [hα, hβ]
  · show _ = _ + ∑ j : Fin (Zt.h + nq), _
    rw [Fin.sum_univ_add]
    simp only [Zonotope.diffusionTimeUpdate, Fin.append_left, Fin.append_right]
    have h1 : ∑ j, α j • (F *ᵥ Zt.G j) = F *ᵥ ∑ j, α j • Zt.G j := by
      rw [mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => (mulVec_smul _ _ _).symm
    rw [h1, hcol Q β, mulVec_add]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
