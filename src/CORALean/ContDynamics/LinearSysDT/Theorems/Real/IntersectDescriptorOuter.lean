import CORALean.ContDynamics.LinearSysDT.Definitions.DescriptorPredictSet
import CORALean.ContDynamics.LinearSysDT.Definitions.MeasurementSet
import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor
import Mathlib.Algebra.BigOperators.Fin

/-!
# The intersection zonotope holds the exact uncertain set

[1, Thm. 1]: with `TE + NC = I` and `TD_d = 0` [1, Eq. 6], every `x₊` of the exact uncertain state
set `X̄₊ ∩ P₊` [1, Def. 3], the prediction of [1, Def. 1] from `⟨p̂, H̄⟩` met with the measurement
set of [1, Def. 2], lies in `⟨p̂₊(Λ), Ĥ₊(Λ)⟩` Eq. 7 of [1, Thm. 1], for every `Λ`. As in the paper's
proof: `x₊ = (TE + NC) x₊ = TA x + TB u + TD ω + N y₊ + NF α`, the unknown input dropping out, and
adding `Λ(y₊ + F α - C x₊) = 0` gives the zonotope's point at the coefficients `(β, ω, α, α)`. The
noise `α` enters twice, as `(I - ΛC)NF α` and `ΛF α`; the zonotope lets the two vary independently,
which is where it is larger than the set.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu nw nd ny nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intersectDescriptor_outer (E T A : Mat ℝ n n) (N Λ : Mat ℝ n ny)
    (B : Mat ℝ n nu) (D : Mat ℝ n nw) (Dd : Mat ℝ n nd) (C : Mat ℝ ny n) (F : Mat ℝ ny nv)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n))
    (hTN : T * E + N * C = 1) (hTD : T * Dd = 0) :
    LinearSysDT.descriptorPredictSet E A B D Dd X.construct u ∩
        LinearSysDT.measurementSet C F y ⊆
      (X.intersectDescriptor T N Λ A B D C F u y).construct := by -- --- PROOF ---
  rintro x ⟨⟨xp, ⟨β, hβ, rfl⟩, ω, hω, d, hE⟩, α, hα, hC⟩
  -- a matrix's columns weighted by a vector are the matrix times it
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (v : Vec ℝ k), ∑ j, v j • (fun i => M i j) = M *ᵥ v :=
    fun M v => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  -- the state, the unknown input decoupled
  have hx : x = T *ᵥ (A *ᵥ (X.c + θ)) + T *ᵥ (B *ᵥ u) + T *ᵥ (D *ᵥ ω) + N *ᵥ y +
      N *ᵥ (F *ᵥ α) := by
    have h1 : x = T *ᵥ (E *ᵥ x) + N *ᵥ (C *ᵥ x) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, hTN, one_mulVec]
    have hd : T *ᵥ (Dd *ᵥ d) = 0 := by rw [mulVec_mulVec, hTD, zero_mulVec]
    have hCx : C *ᵥ x = y + F *ᵥ α := by rw [← hC]; abel
    rw [h1, hE, hCx]
    simp only [mulVec_add, hd, add_zero]
    abel
  refine ⟨Fin.append (Fin.append (Fin.append β ω) α) α, ?_, ?_⟩
  · -- every coefficient is in `[-1, 1]`
    intro j
    refine Fin.addCases (fun j => Fin.addCases (fun j => Fin.addCases (fun j => ?_)
      (fun j => ?_) j) (fun j => ?_) j) (fun j => ?_) j <;> simp [hβ, hω, hα]
  · -- the four generator blocks summed, and the correction `Λ(y + Fα - Cx) = 0` added
    show x = _ + ∑ j : Fin (X.h + nw + nv + nv), _
    rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.intersectDescriptor, Fin.append_left, Fin.append_right]
    have hA : ∑ j, β j • ((1 - Λ * C) *ᵥ (T *ᵥ (A *ᵥ X.G j))) =
        (1 - Λ * C) *ᵥ (T *ᵥ (A *ᵥ θ)) := by
      simp only [θ, mulVec_sum, mulVec_smul]
    rw [hA, hcol, hcol, hcol]
    have hCx : C *ᵥ x = y + F *ᵥ α := by rw [← hC]; abel
    -- what is left is the identity `x = x - Λ(Cx) + Λ(y + Fα)`
    have hsum : T *ᵥ (A *ᵥ X.c) + T *ᵥ (B *ᵥ u) + T *ᵥ (A *ᵥ θ) + T *ᵥ (D *ᵥ ω) +
        N *ᵥ (F *ᵥ α) = x - N *ᵥ y := by
      rw [hx]; simp only [mulVec_add]; abel
    have hΛ : Λ *ᵥ (C *ᵥ x) = Λ *ᵥ y + Λ *ᵥ (F *ᵥ α) := by rw [hCx, mulVec_add]
    have hK : ∀ w, (1 - Λ * C) *ᵥ w = w - Λ *ᵥ (C *ᵥ w) := fun w => by
      simp [sub_mulVec, mulVec_mulVec]
    calc x = (x - N *ᵥ y) - Λ *ᵥ (C *ᵥ (x - N *ᵥ y)) + N *ᵥ y + Λ *ᵥ y - Λ *ᵥ (C *ᵥ (N *ᵥ y)) +
          Λ *ᵥ (F *ᵥ α) := by
          rw [mulVec_sub, mulVec_sub, hΛ]; abel
      _ = _ := by
          rw [← hsum]
          simp only [hK, ← mulVec_mulVec, sub_mulVec, add_mulVec, mulVec_add]
          abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
