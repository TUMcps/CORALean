module

public import CORALean.ContSet.Zonotope.Real.Operations.CorrectedStep
public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The P-radius contraction of the corrected zonotope

[1, Thm. 1]: if `P ≻ 0`, `Y`, diagonal `Γ, Υ ≽ 0` and `γ`, `ε` satisfy `tr Γ + tr Υ < ε` (Eq. 14a)
and the matrix inequality Eq. 14b, `[γP ⋆ ⋆ ⋆; (P - YC)A  P ⋆ ⋆; 0  D_wᵀ(P - YC)ᵀ  Γ ⋆;
0  D_vᵀYᵀ  0  Υ] ≻ 0`, then at `Λ = P⁻¹Y` the P-radius of the zonotope of [1, Prop. 2] satisfies
`V(X(k)) ≤ γ V(X(k-1)) + ε` (Eq. 15), `V = Zonotope.pRadius`. The paper's `γ ∈ (0, 1)` is not
used: `γ ≥ 0` suffices. As in the paper's proof, a point of the new zonotope is its center plus
`d = P⁻¹ R v`, `R = [(P - YC)A  (P - YC)D_w  Y D_v]`, `v = (θ, ϖ, σ)`, so `‖d‖²_P = vᵀ Rᵀ P⁻¹ R v`;
the Schur complement of Eq. 14b at `(θ, -d, ϖ, σ)` and the box bounds give Eq. 15. `D_w` has `n`
rows; the paper prints it `m_w × m_w`. The `k → ∞` clause is `LinearSysDT.radius_ultimate_bound`.

## Inputs
* `A` – state matrix
* `B` – input matrix
* `Dw` – disturbance generator matrix
* `C` – output matrix
* `Dv` – noise generator matrix
* `u` – control input
* `y` – measurement
* `X` – state zonotope
* `P` – weight matrix
* `Y` – gain factor
* `Γ` – disturbance weights
* `Υ` – noise weights
* `γ` – contraction rate
* `ε` – additive bound

## Hypotheses
* `hP` – `P` positive definite
* `hLMI` – linear matrix inequality holds
* `hΓ` – disturbance weights nonnegative
* `hΥ` – noise weights nonnegative
* `hε` – weights sum below `ε`
* `hγ` – rate nonnegative

## Conclusion
* the corrected P-radius is at most `γ` times the old one plus `ε`

## References

* [1] Y. Wang, T. Alamo, V. Puig and G. Cembrano. "A distributed set-membership approach based on
      zonotopes for interconnected systems". 2018 IEEE Conference on Decision and Control (CDC),
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The matrix inequality read at `(θ, -d, ϖ, σ)`: the Schur complement of the block `P`. -/
private theorem Zonotope.aux_pRadius_lmi_form (P R₁ : Mat ℝ n n)
    (Rd : Matrix (Fin n) (Fin nw ⊕ Fin nv) ℝ) (γ : ℝ) (Γ : Vec ℝ nw) (Υ : Vec ℝ nv)
    (hM : (fromBlocks (fromBlocks (γ • P) R₁ᵀ R₁ P)
      (fromRows (0 : Matrix (Fin n) (Fin nw ⊕ Fin nv) ℝ) Rd)
      (fromRows (0 : Matrix (Fin n) (Fin nw ⊕ Fin nv) ℝ) Rd)ᵀ (diagonal (Sum.elim Γ Υ))).PosSemidef)
    (θ d : Vec ℝ n) (ϖ : Vec ℝ nw) (σ : Vec ℝ nv)
    (hd : P *ᵥ d = R₁ *ᵥ θ + Rd *ᵥ Sum.elim ϖ σ) : -- --- CONCL ---
    d ⬝ᵥ (P *ᵥ d) ≤
      γ * (θ ⬝ᵥ (P *ᵥ θ)) + ∑ i, Γ i * ϖ i ^ 2 + ∑ i, Υ i * σ i ^ 2 := by -- --- PROOF ---
  have hdiag : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (e w : ι → ℝ),
      w ⬝ᵥ (diagonal e *ᵥ w) = ∑ i, e i * w i ^ 2 := fun e w => by
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpsd := (posSemidef_iff_dotProduct_mulVec.mp hM).2
    (Sum.elim (Sum.elim θ (-d)) (Sum.elim ϖ σ))
  simp only [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim, fromRows_mulVec,
    transpose_fromRows, fromCols_mulVec, zero_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, Sum.elim_comp_inl, Sum.elim_comp_inr,
    mulVec_neg, dotProduct_neg, hdiag, dotProduct_zero,
    transpose_zero, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hpsd
  have e1 : θ ⬝ᵥ (R₁ᵀ *ᵥ d) = (R₁ *ᵥ θ) ⬝ᵥ d := by rw [dotProduct_mulVec, vecMul_transpose]
  have e2 : (Sum.elim ϖ σ) ⬝ᵥ (Rdᵀ *ᵥ d) = (Rd *ᵥ Sum.elim ϖ σ) ⬝ᵥ d := by
    rw [dotProduct_mulVec, vecMul_transpose]
  have e3 : d ⬝ᵥ (R₁ *ᵥ θ) = (R₁ *ᵥ θ) ⬝ᵥ d := dotProduct_comm _ _
  have e4 : d ⬝ᵥ (Rd *ᵥ Sum.elim ϖ σ) = (Rd *ᵥ Sum.elim ϖ σ) ⬝ᵥ d := dotProduct_comm _ _
  have e5 : d ⬝ᵥ (P *ᵥ d) = d ⬝ᵥ (R₁ *ᵥ θ) + d ⬝ᵥ (Rd *ᵥ Sum.elim ϖ σ) := by
    rw [hd, dotProduct_add]
  simp only [neg_dotProduct] at hpsd
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.correctedStep_pRadius_le (A : Mat ℝ n n) (B : Mat ℝ n nu) (Dw : Mat ℝ n nw)
    (C : Mat ℝ ny n) (Dv : Mat ℝ ny nv) (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n))
    (P : Mat ℝ n n) (Y : Mat ℝ n ny) (Γ : Vec ℝ nw) (Υ : Vec ℝ nv) (γ ε : ℝ) (hP : P.PosDef)
    (hLMI : (fromBlocks (fromBlocks (γ • P) ((P - Y * C) * A)ᵀ ((P - Y * C) * A) P)      -- Eq. 14b
      (fromRows (0 : Matrix (Fin n) (Fin nw ⊕ Fin nv) ℝ)
        (fromCols ((P - Y * C) * Dw) (Y * Dv)))
      (fromRows (0 : Matrix (Fin n) (Fin nw ⊕ Fin nv) ℝ)
        (fromCols ((P - Y * C) * Dw) (Y * Dv)))ᵀ (diagonal (Sum.elim Γ Υ))).PosDef)
    (hΓ : ∀ i, 0 ≤ Γ i) (hΥ : ∀ i, 0 ≤ Υ i) (hε : ∑ i, Γ i + ∑ i, Υ i < ε)        -- Eq. 14a
    (hγ : 0 ≤ γ) : -- --- CONCL ---
    (X.correctedStep (P⁻¹ * Y) A B Dw C Dv u y).pRadius P ≤
      γ * X.pRadius P + ε := by -- --- PROOF ---
  haveI : Invertible P := hP.isUnit.invertible
  set Z := X.correctedStep (P⁻¹ * Y) A B Dw C Dv u y
  -- the radius of `X` bounds every offset
  have hbdd : BddAbove ((fun z => (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c))) '' X.construct) := by
    refine (X.isCompact_construct.image ?_).bddAbove
    have h : Continuous fun z : Vec ℝ n => z - X.c := continuous_id.sub continuous_const
    exact h.dotProduct (continuous_const.matrix_mulVec h)
  refine csSup_le ⟨_, Z.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∃ b : Fin (X.h + nw + nv) → ℝ, (∀ j, |b j| ≤ 1) ∧
      z = Z.c + ∑ j : Fin (X.h + nw + nv), b j • Z.G j := hz
  obtain ⟨b, hb, rfl⟩ := hz'
  set β : Fin X.h → ℝ := fun j => b (Fin.castAdd nv (Fin.castAdd nw j))
  set ϖ : Vec ℝ nw := fun j => b (Fin.castAdd nv (Fin.natAdd X.h j))
  set σ : Vec ℝ nv := fun j => b (Fin.natAdd (X.h + nw) j)
  set θ : Vec ℝ n := ∑ j, β j • X.G j
  -- the coefficients of the point: the offset `θ` in `X`, the disturbance, the noise
  have hcol : ∀ {k : ℕ} (M : Mat ℝ n k) (w : Vec ℝ k), ∑ j, w j • (fun i => M i j) = M *ᵥ w :=
    fun M w => by ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  -- the offset of the point, `d = (I - ΛC) A θ + (I - ΛC) D_w ϖ + Λ D_v σ`
  set d : Vec ℝ n := ((1 - (P⁻¹ * Y) * C) * A) *ᵥ θ + ((1 - (P⁻¹ * Y) * C) * Dw) *ᵥ ϖ +
    ((P⁻¹ * Y) * Dv) *ᵥ σ with hd
  have hoff : Z.c + ∑ j : Fin (X.h + nw + nv), b j • Z.G j - Z.c = d := by
    rw [add_sub_cancel_left, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Z, Zonotope.correctedStep, Fin.append_left, Fin.append_right]
    have hA : ∑ j, β j • ((1 - P⁻¹ * Y * C) *ᵥ (A *ᵥ X.G j)) =
        ((1 - (P⁻¹ * Y) * C) * A) *ᵥ θ := by
      simp only [θ, mulVec_sum, mulVec_smul, mulVec_mulVec]
    simp only [β] at hA
    rw [hA, hcol, hcol]
  -- `P d = R v`
  have hPd : P *ᵥ d = ((P - Y * C) * A) *ᵥ θ +
      (fromCols ((P - Y * C) * Dw) (Y * Dv)) *ᵥ Sum.elim ϖ σ := by
    rw [fromCols_mulVec, hd]
    simp only [mulVec_add, mulVec_mulVec]
    have hPY : P * (P⁻¹ * Y) = Y := by
      rw [← Matrix.mul_assoc, mul_inv_of_invertible, Matrix.one_mul]
    have hPK : P * (1 - P⁻¹ * Y * C) = P - Y * C := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPY]
    rw [show P * ((1 - P⁻¹ * Y * C) * A) = (P - Y * C) * A by rw [← Matrix.mul_assoc, hPK],
      show P * ((1 - P⁻¹ * Y * C) * Dw) = (P - Y * C) * Dw by rw [← Matrix.mul_assoc, hPK],
      show P * (P⁻¹ * Y * Dv) = Y * Dv by rw [← Matrix.mul_assoc, hPY]]
    abel
  -- the matrix inequality at `(θ, -d, ϖ, σ)` bounds `dᵀPd`
  have hlmi := Zonotope.aux_pRadius_lmi_form P ((P - Y * C) * A)
    (fromCols ((P - Y * C) * Dw) (Y * Dv)) γ Γ Υ hLMI.posSemidef θ d ϖ σ hPd
  -- `θᵀPθ ≤ V(X(k-1))`, and the box bounds on `ϖ`, `σ`
  have hθ : θ ⬝ᵥ (P *ᵥ θ) ≤ X.pRadius P := by
    refine le_csSup hbdd ⟨X.c + θ, ⟨β, fun j => hb _, rfl⟩, ?_⟩
    simp
  have hbox : ∀ {k : ℕ} (g w : Vec ℝ k), (∀ i, 0 ≤ g i) → (∀ i, |w i| ≤ 1) →
      ∑ i, g i * w i ^ 2 ≤ ∑ i, g i := fun g w hg hw =>
    Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hg i)
      ((sq_le_one_iff_abs_le_one _).mpr (hw i))
  have h₁ := hbox Γ ϖ hΓ fun i => hb _
  have h₂ := hbox Υ σ hΥ fun i => hb _
  have hγθ := mul_le_mul_of_nonneg_left hθ hγ
  beta_reduce
  rw [hoff]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
