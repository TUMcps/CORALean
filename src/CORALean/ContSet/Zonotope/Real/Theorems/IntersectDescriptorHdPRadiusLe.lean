module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor
public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.Global.PosDefSchurComplement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The P-radius contraction of the LPV estimator

[1, Thm. 2], corrected. The intersection zonotope of [1, Thm. 1] has four generator blocks,
`(I - ΛC)TA Ĥ`, `(I - ΛC)TD H_d`, `(I - ΛC)NF H_d` and `ΛF H_d` (its Eq. 10), each with its own
coefficients. If `P ≻ 0` and the matrix inequality
`[αP ⋆ ⋆ ⋆ ⋆; 0 (1-α)β₁I ⋆ ⋆ ⋆; 0 0 (1-α)β₂I ⋆ ⋆; 0 0 0 (1-α)β₃I ⋆;
P(I-ΛC)TA  P(I-ΛC)TD  P(I-ΛC)NF  PΛF  P] ≻ 0` holds with `β₁ + β₂ + β₃ = 1`, then
`ϱ_k ≤ α ϱ_{k-1} + (1 - α) ℓ_d` (its Eq. 21a), and if `I ≼ γ² P` (its Eq. 26) then
`ℓ_k ≤ γ² ϱ_k` (its Eq. 21b); `ϱ` is the P-radius, `ℓ` the radius (`pRadius` at `I`), `ϱ_{k-1}`
any bound of the P-radius of `X̂_{k-1}` and `ℓ_d` any bound of `‖H_d b‖²` on the unit box. The
paper's Eq. 19 gives the last two blocks one coefficient and one weight `(1-α)(1-β)`, which
fails (`intersectDescriptorHd_pRadius_counterexample`); its Eq. 20 has no solution
(`LinearSysDT.radiusLmi_infeasible`). As in the paper's proof: a point's offset is `P⁻¹ R v`,
`v = (Ĥz̄, H_d b₁, H_d b₂, H_d b₃)`, and the Schur complement of `P` bounds `vᵀRᵀP⁻¹Rv`.

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu ny nd m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectDescriptorHd_pRadius_le (T : Mat ℝ n n) (N Λ : Mat ℝ n ny)
    (A : Mat ℝ n n) (B : Mat ℝ n nu) (D : Mat ℝ n nd) (C : Mat ℝ ny n) (F : Mat ℝ ny nd)
    (Hd : Mat ℝ nd m) (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (P : Mat ℝ n n)
    (α β₁ β₂ β₃ γ ϱ ℓd : ℝ) (hP : P.PosDef)
    (hLMI :
      let Dg : Matrix (Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd)))
          (Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd))) ℝ :=
        fromBlocks (α • P) 0 0 (fromBlocks (((1 - α) * β₁) • 1) 0 0
          (fromBlocks (((1 - α) * β₂) • 1) 0 0 (((1 - α) * β₃) • 1)))
      let R : Matrix (Fin n) (Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd))) ℝ :=
        fromCols (P * (1 - Λ * C) * T * A) (fromCols (P * (1 - Λ * C) * T * D)
          (fromCols (P * (1 - Λ * C) * N * F) (P * Λ * F)))
      (fromBlocks Dg Rᵀ R P).PosDef)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hβ₃ : 0 ≤ β₃)
    (hβ : β₁ + β₂ + β₃ = 1)
    (hϱ : ∀ z ∈ X.construct, (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c)) ≤ ϱ)
    (hℓd : ∀ b : Vec ℝ m, (∀ i, |b i| ≤ 1) → (Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b) ≤ ℓd)
    (hγ : ∀ x : Vec ℝ n, x ⬝ᵥ x ≤ γ ^ 2 * (x ⬝ᵥ (P *ᵥ x))) : -- --- STMT ---
    let Z := X.intersectDescriptor T N Λ A B (D * Hd) C (F * Hd) u y
    Z.pRadius P ≤ α * ϱ + (1 - α) * ℓd ∧ Z.pRadius 1 ≤ γ ^ 2 * Z.pRadius P := by -- --- PROOF ---
  intro Z
  set Dg : Matrix (Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd))) (Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd))) ℝ :=
    fromBlocks (α • P) 0 0 (fromBlocks (((1 - α) * β₁) • 1) 0 0
      (fromBlocks (((1 - α) * β₂) • 1) 0 0 (((1 - α) * β₃) • 1))) with hDg
  set R : Matrix (Fin n) (Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd))) ℝ :=
    fromCols (P * (1 - Λ * C) * T * A) (fromCols (P * (1 - Λ * C) * T * D)
      (fromCols (P * (1 - Λ * C) * N * F) (P * Λ * F))) with hR
  haveI : Invertible P := hP.isUnit.invertible
  -- the Schur complement of the block `P`
  have hS : (Dg - Rᵀ * P⁻¹ * R).PosDef := by
    have h := posDef_schur_of_fromBlocks Dg Rᵀ hP (by rw [transpose_transpose]; exact hLMI)
    rwa [transpose_transpose] at h
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (w : Vec ℝ k), ∑ j, w j • (fun i => M i j) = M *ᵥ w :=
    fun M w => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  have hPi : ∀ {k : ℕ} (M : Mat ℝ n k), P⁻¹ * (P * M) = M := fun M => by
    rw [← Matrix.mul_assoc, inv_mul_of_invertible, Matrix.one_mul]
  -- every point's P-form is at most `α ϱ + (1 - α) ℓ_d`
  have hpt : ∀ z ∈ Z.construct, (z - Z.c) ⬝ᵥ (P *ᵥ (z - Z.c)) ≤ α * ϱ + (1 - α) * ℓd := by
    intro z hz
    have hz' : ∃ b : Fin (X.h + m + m + m) → ℝ, (∀ j, |b j| ≤ 1) ∧
        z = Z.c + ∑ j : Fin (X.h + m + m + m), b j • Z.G j := hz
    obtain ⟨b, hb, rfl⟩ := hz'
    -- the coefficients of the four blocks
    set β : Fin X.h → ℝ := fun j => b (Fin.castAdd m (Fin.castAdd m (Fin.castAdd m j)))
    set b₁ : Vec ℝ m := fun j => b (Fin.castAdd m (Fin.castAdd m (Fin.natAdd X.h j)))
    set b₂ : Vec ℝ m := fun j => b (Fin.castAdd m (Fin.natAdd (X.h + m) j))
    set b₃ : Vec ℝ m := fun j => b (Fin.natAdd (X.h + m + m) j)
    set θ : Vec ℝ n := ∑ j, β j • X.G j
    set v : Fin n ⊕ (Fin nd ⊕ (Fin nd ⊕ Fin nd)) → ℝ :=
      Sum.elim θ (Sum.elim (Hd *ᵥ b₁) (Sum.elim (Hd *ᵥ b₂) (Hd *ᵥ b₃)))
    -- the point's offset is `P⁻¹ R v`
    have hoff : Z.c + ∑ j : Fin (X.h + m + m + m), b j • Z.G j - Z.c = P⁻¹ *ᵥ (R *ᵥ v) := by
      rw [add_sub_cancel_left, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
      simp only [Z, Zonotope.intersectDescriptor, Fin.append_left, Fin.append_right]
      have hA : ∑ j, β j • ((1 - Λ * C) *ᵥ (T *ᵥ (A *ᵥ X.G j))) =
          (1 - Λ * C) *ᵥ (T *ᵥ (A *ᵥ θ)) := by
        simp only [θ, mulVec_sum, mulVec_smul]
      simp only [β] at hA
      rw [hA, hcol, hcol, hcol]
      simp only [hR, v, fromCols_mulVec_sumElim, mulVec_add, mulVec_mulVec, hPi, b₁, b₂, b₃,
        Matrix.mul_assoc]
      abel
    -- `‖P⁻¹ R v‖²_P = vᵀ Rᵀ P⁻¹ R v`
    have hq : (P⁻¹ *ᵥ (R *ᵥ v)) ⬝ᵥ (P *ᵥ (P⁻¹ *ᵥ (R *ᵥ v))) = v ⬝ᵥ ((Rᵀ * P⁻¹ * R) *ᵥ v) := by
      have hPP : P *ᵥ (P⁻¹ *ᵥ (R *ᵥ v)) = R *ᵥ v := by
        rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
      rw [hPP, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v, vecMul_transpose,
        dotProduct_comm]
    -- `vᵀ Dg v`, block by block
    have hDv : v ⬝ᵥ (Dg *ᵥ v) = α * (θ ⬝ᵥ (P *ᵥ θ)) +
        (1 - α) * β₁ * ((Hd *ᵥ b₁) ⬝ᵥ (Hd *ᵥ b₁)) + (1 - α) * β₂ * ((Hd *ᵥ b₂) ⬝ᵥ (Hd *ᵥ b₂)) +
        (1 - α) * β₃ * ((Hd *ᵥ b₃) ⬝ᵥ (Hd *ᵥ b₃)) := by
      simp only [hDg, v, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec,
        add_zero, zero_add, sumElim_dotProduct_sumElim, smul_mulVec, one_mulVec, dotProduct_smul,
        smul_eq_mul]
      ring
    -- the Schur complement at `v`, then the bounds on each block
    have hpsd := (posSemidef_iff_dotProduct_mulVec.mp hS.posSemidef).2 v
    rw [star_trivial, sub_mulVec, dotProduct_sub, hDv] at hpsd
    have hθ : θ ⬝ᵥ (P *ᵥ θ) ≤ ϱ := by
      have h := hϱ (X.c + θ) ⟨β, fun j => hb _, rfl⟩
      rwa [add_sub_cancel_left] at h
    have h₁ := hℓd b₁ fun i => hb _
    have h₂ := hℓd b₂ fun i => hb _
    have h₃ := hℓd b₃ fun i => hb _
    have hc : 0 ≤ 1 - α := by linarith
    have e1 := mul_le_mul_of_nonneg_left hθ hα0
    have e2 := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hc hβ₁)
    have e3 := mul_le_mul_of_nonneg_left h₂ (mul_nonneg hc hβ₂)
    have e4 := mul_le_mul_of_nonneg_left h₃ (mul_nonneg hc hβ₃)
    have hsum : α * ϱ + (1 - α) * β₁ * ℓd + (1 - α) * β₂ * ℓd + (1 - α) * β₃ * ℓd =
        α * ϱ + (1 - α) * ℓd := by
      linear_combination (1 - α) * ℓd * hβ
    rw [hoff, hq]
    linarith
  -- the zonotope is nonempty, and the P-form bounded on it
  have hne : ((fun z => (z - Z.c) ⬝ᵥ (P *ᵥ (z - Z.c))) '' Z.construct).Nonempty :=
    ⟨_, Z.c, ⟨0, by simp, by simp⟩, rfl⟩
  have hbdd : BddAbove ((fun z => (z - Z.c) ⬝ᵥ (P *ᵥ (z - Z.c))) '' Z.construct) :=
    ⟨_, by rintro _ ⟨z, hz, rfl⟩; exact hpt z hz⟩
  refine ⟨csSup_le hne (by rintro _ ⟨z, hz, rfl⟩; exact hpt z hz), ?_⟩
  -- the theorem's Eq. 26 point by point
  refine csSup_le ⟨_, Z.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have h1 := hγ (z - Z.c)
  have h2 := le_csSup hbdd ⟨z, hz, rfl⟩
  simp only [one_mulVec]
  calc (z - Z.c) ⬝ᵥ (z - Z.c) ≤ γ ^ 2 * ((z - Z.c) ⬝ᵥ (P *ᵥ (z - Z.c))) := h1
    _ ≤ γ ^ 2 * Z.pRadius P := mul_le_mul_of_nonneg_left h2 (sq_nonneg γ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
