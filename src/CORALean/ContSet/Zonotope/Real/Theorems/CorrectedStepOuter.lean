module

public import CORALean.ContSet.Zonotope.Real.Operations.CorrectedStep
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The corrected zonotope holds the next state

[1, Prop. 2]: if `x(k-1) ∈ ⟨c(k-1), H(k-1)⟩`, then for every correction matrix `Λ`,
`x(k) ∈ ⟨c(k), H(k)⟩` Eq. 13 of [1, Prop. 2], `c(k) = (I - ΛC)(A c(k-1) + B u(k-1)) + Λ y(k)` and
`H(k) = [(I - ΛC) A H(k-1)  (I - ΛC) D_w  Λ D_v]`. The paper omits the proof as that of
[1, Prop. 1]: `x(k) = A x(k-1) + B u(k-1) + w`, and adding `Λ(y(k) - C x(k) - v) = 0` leaves `x(k)`
at the zonotope's point with coefficients `(θ, ϖ, -σ)`, where `w = D_w ϖ` and `v = D_v σ`.

## Inputs
* `Λ` – correction matrix
* `A` – state matrix
* `B` – input matrix
* `Dw` – disturbance generator matrix
* `C` – output matrix
* `Dv` – noise generator matrix
* `u` – control input
* `y` – measurement
* `X` – state zonotope
* `x` – state
* `ϖ` – disturbance coefficients
* `σ` – noise coefficients

## Hypotheses
* `hx` – state lies in `X`
* `hϖ` – disturbance coefficients within the unit box
* `hσ` – noise coefficients within the unit box
* `hy` – measurement is consistent with the state

## Conclusion
* the next state lies in the corrected zonotope

## References

* [1] Y. Wang, T. Alamo, V. Puig and G. Cembrano. "A distributed set-membership approach based on
      zonotopes for interconnected systems". 2018 IEEE Conference on Decision and Control (CDC),
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.correctedStep_outer (Λ : Mat ℝ n ny) (A : Mat ℝ n n) (B : Mat ℝ n nu)
    (Dw : Mat ℝ n nw) (C : Mat ℝ ny n) (Dv : Mat ℝ ny nv) (u : Vec ℝ nu) (y : Vec ℝ ny)
    (X : Zonotope (Vec ℝ n)) (x : Vec ℝ n) (hx : x ∈ X.construct) (ϖ : Vec ℝ nw)
    (hϖ : ∀ j, |ϖ j| ≤ 1) (σ : Vec ℝ nv) (hσ : ∀ j, |σ j| ≤ 1)
    (hy : y = C *ᵥ (A *ᵥ x + B *ᵥ u + Dw *ᵥ ϖ) + Dv *ᵥ σ) : -- --- CONCL ---
    A *ᵥ x + B *ᵥ u + Dw *ᵥ ϖ ∈ (X.correctedStep Λ A B Dw C Dv u y).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  -- the offset `θ` of `x(k-1)` in `X`, and the state `x(k)` to enclose
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  set x' : Vec ℝ n := A *ᵥ (X.c + θ) + B *ᵥ u + Dw *ᵥ ϖ with hx'
  refine ⟨Fin.append (Fin.append β ϖ) (fun j => -σ j), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j) (fun j => ?_) j <;>
      simp [hβ, hϖ, hσ]
  · -- the three generator blocks summed
    show x' = _ + ∑ j : Fin (X.h + nw + nv), _
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.correctedStep, Fin.append_left, Fin.append_right]
    have hA : ∑ j, β j • ((1 - Λ * C) *ᵥ (A *ᵥ X.G j)) = (1 - Λ * C) *ᵥ (A *ᵥ θ) := by
      simp only [θ, mulVec_sum, mulVec_smul]
    -- the last block is `-Λ D_v σ`
    have h3 : ∑ j, (-σ j) • (fun i => (Λ * Dv) i j) = -((Λ * Dv) *ᵥ σ) := by
      rw [← mulVec_neg, ← hcol]; rfl
    rw [hA, hcol, h3]
    -- adding `Λ(y - C x(k) - D_v σ) = 0` to the prediction
    have hK : ∀ w, (1 - Λ * C) *ᵥ w = w - Λ *ᵥ (C *ᵥ w) := fun w => by
      simp [sub_mulVec, mulVec_mulVec]
    have hΛ : Λ *ᵥ y = Λ *ᵥ (C *ᵥ x') + (Λ * Dv) *ᵥ σ := by
      rw [hy, mulVec_add, ← mulVec_mulVec]
    rw [hΛ]
    -- the state as the center, its offset and the disturbance
    have hxe : x' = (A *ᵥ X.c + B *ᵥ u) + A *ᵥ θ + Dw *ᵥ ϖ := by
      simp only [hx', mulVec_add]; abel
    have key : (1 - Λ * C) *ᵥ (A *ᵥ X.c + B *ᵥ u) + (1 - Λ * C) *ᵥ A *ᵥ θ +
        ((1 - Λ * C) * Dw) *ᵥ ϖ = (1 - Λ * C) *ᵥ x' := by
      rw [hxe]; simp only [mulVec_add, mulVec_mulVec]
    -- what is left is `x' = (I - ΛC) x' + Λ C x'`
    have e1 : (1 - Λ * C) *ᵥ (A *ᵥ X.c + B *ᵥ u) + (Λ *ᵥ C *ᵥ x' + (Λ * Dv) *ᵥ σ) +
        ((1 - Λ * C) *ᵥ A *ᵥ θ + ((1 - Λ * C) * Dw) *ᵥ ϖ + -((Λ * Dv) *ᵥ σ)) =
        ((1 - Λ * C) *ᵥ (A *ᵥ X.c + B *ᵥ u) + (1 - Λ * C) *ᵥ A *ᵥ θ +
          ((1 - Λ * C) * Dw) *ᵥ ϖ) + Λ *ᵥ C *ᵥ x' := by abel
    rw [e1, key, hK]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
