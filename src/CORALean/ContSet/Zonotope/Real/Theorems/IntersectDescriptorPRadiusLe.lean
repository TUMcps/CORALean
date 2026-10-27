module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor
public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.Global.PosDefSchurComplement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The W-radius criterion of the offline correction matrix

[1, Thm. 3]: if `W ≻ 0`, `Y` and diagonal `Γ, Υ, Ω ≻ 0` (Eq. 19) satisfy the matrix inequality
Eq. 18, `[γW 0 0 0 ⋆; 0 Γ 0 0 ⋆; 0 0 Υ 0 ⋆; 0 0 0 Ω ⋆; (W - YC)TA  (W - YC)TD  (W - YC)NF  YF  W]
≻ 0`, with `tr Γ + tr Υ + tr Ω < ε` (Eq. 20), then at `Λ = W⁻¹ Y` the W-radius of the
intersection zonotope satisfies `ℓ_{W+} ≤ γ ℓ_W + ε` (Eq. 17); any bound `ℓ` of `⟨p̂, H̄⟩`'s does,
and `γ ≥ 0` suffices. As in the paper's proof, a point's offset is `W⁻¹ R̃ (H̄z̄, b₁, b₂, b₃)`
(`Y = WΛ`, Eq. 22), and the Schur complement of the block `W` (`posDef_schur_of_fromBlocks`)
bounds its W-norm by `γ ‖H̄z̄‖²_W + b₁ᵀΓb₁ + b₂ᵀΥb₂ + b₃ᵀΩb₃`. The blocks are sized by what they
multiply (`Γ` is `n_w × n_w`, `Υ, Ω` `n_v × n_v`; box of [1, Eq. 16]), not `n_x`, `n_y` as printed.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – control input
* `y` – measurement
* `X` – state zonotope
* `W` – weight matrix
* `Y` – gain factor
* `Γ` – disturbance weights
* `Υ` – noise weights
* `Ω` – second noise weights
* `γ` – contraction rate
* `ε` – additive bound
* `ℓ` – bound on the radius of `X`

## Hypotheses
* `hW` – `W` positive definite
* `hLMI` – linear matrix inequality holds
* `hΓ` – disturbance weights positive
* `hΥ` – noise weights positive
* `hΩ` – second noise weights positive
* `hε` – weights sum below `ε`
* `hγ` – rate nonnegative
* `hℓ` – `X` has W-radius at most `ℓ`

## Conclusion
* the new W-radius is at most `γ ℓ + ε`

## References

* [1] [Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica,
      2018.](../../../../../../references/2018/wang-automatica-descriptor-observer.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectDescriptor_pRadius_le (T : Mat ℝ n n) (N : Mat ℝ n ny)
    (A : Mat ℝ n n) (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (W : Mat ℝ n n) (Y : Mat ℝ n ny)
    (Γ : Vec ℝ nw) (Υ Ω : Vec ℝ nv) (γ ε ℓ : ℝ) (hW : W.PosDef)
    (hLMI :
      let R : Matrix (Fin n) (Fin n ⊕ (Fin nw ⊕ (Fin nv ⊕ Fin nv))) ℝ :=           -- Eq. 22
        fromCols ((W - Y * C) * T * A)
          (fromCols ((W - Y * C) * T * D) (fromCols ((W - Y * C) * N * F) (Y * F)))
      (fromBlocks (fromBlocks (γ • W) 0 0 (diagonal (Sum.elim Γ (Sum.elim Υ Ω)))) Rᵀ R W).PosDef)
    (hΓ : ∀ i, 0 < Γ i) (hΥ : ∀ i, 0 < Υ i) (hΩ : ∀ i, 0 < Ω i)                 -- Eq. 19
    (hε : ∑ i, Γ i + ∑ i, Υ i + ∑ i, Ω i < ε)                                    -- Eq. 20
    (hγ : 0 ≤ γ) (hℓ : ∀ z ∈ X.construct, (z - X.c) ⬝ᵥ (W *ᵥ (z - X.c)) ≤ ℓ) : -- --- CONCL ---
    (X.intersectDescriptor T N (W⁻¹ * Y) A B D C F u y).pRadius W ≤
      γ * ℓ + ε := by -- --- PROOF ---
  set R : Matrix (Fin n) (Fin n ⊕ (Fin nw ⊕ (Fin nv ⊕ Fin nv))) ℝ :=
    fromCols ((W - Y * C) * T * A)
      (fromCols ((W - Y * C) * T * D) (fromCols ((W - Y * C) * N * F) (Y * F))) with hR
  set Dg : Matrix (Fin n ⊕ (Fin nw ⊕ (Fin nv ⊕ Fin nv))) (Fin n ⊕ (Fin nw ⊕ (Fin nv ⊕ Fin nv))) ℝ :=
    fromBlocks (γ • W) 0 0 (diagonal (Sum.elim Γ (Sum.elim Υ Ω))) with hDg
  set Z := X.intersectDescriptor T N (W⁻¹ * Y) A B D C F u y
  haveI : Invertible W := hW.isUnit.invertible
  -- the Schur complement of the block `W`
  have hS : (Dg - Rᵀ * W⁻¹ * R).PosDef := by
    have h := posDef_schur_of_fromBlocks Dg Rᵀ hW (by rw [transpose_transpose]; exact hLMI)
    rwa [transpose_transpose] at h
  have hWT : Wᵀ = W := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hW.isHermitian.eq
  have hWiT : (W⁻¹)ᵀ = W⁻¹ := by rw [transpose_nonsing_inv, hWT]
  have hK : W⁻¹ * (W - Y * C) = 1 - W⁻¹ * Y * C := by
    rw [Matrix.mul_sub, inv_mul_of_invertible, Matrix.mul_assoc]
  refine csSup_le ⟨_, Z.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∃ b : Fin (X.h + nw + nv + nv) → ℝ, (∀ j, |b j| ≤ 1) ∧
      z = Z.c + ∑ j : Fin (X.h + nw + nv + nv), b j • Z.G j := hz
  obtain ⟨b, hb, rfl⟩ := hz'
  -- the coefficients of the four blocks
  set β : Fin X.h → ℝ := fun j => b (Fin.castAdd nv (Fin.castAdd nv (Fin.castAdd nw j)))
  set b₁ : Vec ℝ nw := fun j => b (Fin.castAdd nv (Fin.castAdd nv (Fin.natAdd X.h j)))
  set b₂ : Vec ℝ nv := fun j => b (Fin.castAdd nv (Fin.natAdd (X.h + nw) j))
  set b₃ : Vec ℝ nv := fun j => b (Fin.natAdd (X.h + nw + nv) j)
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  set v : Fin n ⊕ (Fin nw ⊕ (Fin nv ⊕ Fin nv)) → ℝ := Sum.elim θ (Sum.elim b₁ (Sum.elim b₂ b₃))
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (w : Vec ℝ k), ∑ j, w j • (fun i => M i j) = M *ᵥ w :=
    fun M w => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  -- the point's offset is `W⁻¹ R v`
  have hoff : Z.c + ∑ j : Fin (X.h + nw + nv + nv), b j • Z.G j - Z.c = W⁻¹ *ᵥ (R *ᵥ v) := by
    rw [add_sub_cancel_left, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Z, Zonotope.intersectDescriptor, Fin.append_left, Fin.append_right]
    have hA : ∑ j, β j • ((1 - W⁻¹ * Y * C) *ᵥ (T *ᵥ (A *ᵥ X.G j))) =
        (1 - W⁻¹ * Y * C) *ᵥ (T *ᵥ (A *ᵥ θ)) := by
      simp only [θ, mulVec_sum, mulVec_smul]
    simp only [β] at hA
    rw [hA, hcol, hcol, hcol]
    simp only [hR, v, fromCols_mulVec_sumElim, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, hK,
      b₁, b₂, b₃]
    abel
  -- `‖W⁻¹ R v‖²_W = (R v)ᵀ W⁻¹ (R v) = vᵀ Rᵀ W⁻¹ R v`
  have hq : (W⁻¹ *ᵥ (R *ᵥ v)) ⬝ᵥ (W *ᵥ (W⁻¹ *ᵥ (R *ᵥ v))) =
      v ⬝ᵥ ((Rᵀ * W⁻¹ * R) *ᵥ v) := by
    have hWW : W *ᵥ (W⁻¹ *ᵥ (R *ᵥ v)) = R *ᵥ v := by
      rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
    rw [hWW, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v, vecMul_transpose,
      dotProduct_comm]
  -- `vᵀ Dg v`, block by block
  have hdiag : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d w : ι → ℝ),
      w ⬝ᵥ (diagonal d *ᵥ w) = ∑ i, d i * w i ^ 2 := fun d w => by
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hDv : v ⬝ᵥ (Dg *ᵥ v) = γ * (θ ⬝ᵥ (W *ᵥ θ)) + ∑ i, Γ i * b₁ i ^ 2 +
      ∑ i, Υ i * b₂ i ^ 2 + ∑ i, Ω i * b₃ i ^ 2 := by
    simp only [hDg, v, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec,
      add_zero, zero_add, sumElim_dotProduct_sumElim, smul_mulVec, dotProduct_smul, smul_eq_mul,
      hdiag, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    ring
  -- the Schur complement at `v`, then the box bounds of Eq. 24
  have hpsd := (posSemidef_iff_dotProduct_mulVec.mp hS.posSemidef).2 v
  rw [star_trivial, sub_mulVec, dotProduct_sub, hDv] at hpsd
  have hθ : θ ⬝ᵥ (W *ᵥ θ) ≤ ℓ := by
    have h := hℓ (X.c + θ) ⟨β, fun j => hb _, rfl⟩
    rwa [add_sub_cancel_left] at h
  have hbox : ∀ {k : ℕ} (g w : Vec ℝ k), (∀ i, 0 < g i) → (∀ i, |w i| ≤ 1) →
      ∑ i, g i * w i ^ 2 ≤ ∑ i, g i := fun g w hg hw =>
    Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hg i).le
      ((sq_le_one_iff_abs_le_one _).mpr (hw i))
  have h₁ := hbox Γ b₁ hΓ fun i => hb _
  have h₂ := hbox Υ b₂ hΥ fun i => hb _
  have h₃ := hbox Ω b₃ hΩ fun i => hb _
  have hγθ := mul_le_mul_of_nonneg_left hθ hγ
  beta_reduce
  rw [hoff, hq]
  linarith


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
