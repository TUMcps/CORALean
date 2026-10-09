import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerUpdate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-!
# The Luenberger step encloses the observer's next state

[1, Thm. 2]: if `x̂ₖ₋₁ ∈ ⟨ĉ, Ĝ⟩`, `nₖ ∈ ⟨0, Q⟩` and `v̄ ∈ ⟨0, R⟩`, then the state of the observer
`xₖ = F xₖ₋₁ + nₖ + Λ (y - Γ xₖ₋₁ - v̄)` Eq. 27 of [1, Thm. 2] lies in `⟨c̄, Ḡ⟩`, for every gain
`Λ` and every measurement `ȳ`. As in the paper: the state is `ĉ` plus the generators of `Ĝ` with
coefficients `α`, and the noises are `Q β` and `R γ`, so `xₖ` is `c̄` plus `(F - Λ Γ) Ĝ α`,
`-Λ R γ` and `Q β`: the coefficients `(α, γ, β)` stay in `[-1, 1]`.

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p nq nr : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.luenbergerUpdate_outer (F : Mat ℝ n n) (Γ : Mat ℝ p n) (Λ : Mat ℝ n p)
    (Q : Mat ℝ n nq) (R : Mat ℝ p nr) (y : Vec ℝ p) (X : Zonotope (Vec ℝ n)) (x : Vec ℝ n)
    (hx : x ∈ X.construct) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1) (γ : Vec ℝ nr)
    (hγ : ∀ j, |γ j| ≤ 1) :
    F *ᵥ x + Q *ᵥ β + Λ *ᵥ (y - Γ *ᵥ x - R *ᵥ γ) ∈
      (Zonotope.luenbergerUpdate F Γ Λ Q R y X).construct := by -- --- PROOF ---
  obtain ⟨α, hα, rfl⟩ := hx
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  -- the coefficients: the previous state's, the measurement noise's and the process noise's
  refine ⟨Fin.append (Fin.append α γ) β, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) (fun j => ?_) j <;>
      simp [hα, hβ, hγ]
  · show _ = _ + ∑ j : Fin (X.h + nr + nq), _
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.luenbergerUpdate, Fin.append_left, Fin.append_right]
    -- the three blocks: `(F - Λ Γ) Ĝ α`, `-Λ R γ` and `Q β`
    have h1 : ∑ j, α j • ((F - Λ * Γ) *ᵥ X.G j) = (F - Λ * Γ) *ᵥ ∑ j, α j • X.G j := by
      rw [mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => (mulVec_smul _ _ _).symm
    have h2 : ∑ j, γ j • (fun i => (-(Λ * R)) i j) = -(Λ *ᵥ (R *ᵥ γ)) := by
      rw [hcol, neg_mulVec, mulVec_mulVec]
    rw [h1, h2, hcol Q β]
    simp only [mulVec_add, mulVec_sub, sub_mulVec, mulVec_mulVec]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
