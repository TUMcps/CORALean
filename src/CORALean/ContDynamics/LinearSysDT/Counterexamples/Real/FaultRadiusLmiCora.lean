module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.QuadFormLeOfFaultRadiusLmi
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# CORA's `PRad-E` matrix is not [1, Eq. 17]

CORA's `@linearSysDT/private/priv_observe_gain_PRadE.m`, which cites [1], assembles [1, Eq. 17]
with `E = generators(W)` for `D_xH_w`, `F = generators(V)` for `D_yH_v` and `Y` for `W`, and sets
its block `(3, 4)` to `F*Y'`, that is `D_yH_v Wᵀ`, where Eq. 17 has `H_vᵀD_yᵀWᵀ` (the transpose
of `F`). With `n_x = 1`, two outputs, no disturbance, `A = C = 0`, `F = [1 1/2; 0 1]`, `P = 9/10`,
`W = [0 1]` and `γ = 1/2`, CORA's matrix is negative definite while Eq. 17 is not: at the gain
`L = P⁻¹W` the step inequality (`LinearSysDT.quadForm_le_of_faultRadiusLmi`) fails at `θ = 0`,
`s₂ = (-1/2, 1)`. A gain CORA accepts need not have the P-radius property; the observer's
enclosure does not depend on the gain (`LinearSysDT.faultObserve_outer`), so only tightness is lost.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's matrix is negative definite while the paper's is not

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The negated form of the block matrix is a sum of squares, positive off `0`. -/
theorem LinearSysDT.aux_faultRadiusLmiCora_sos (θ s₀ s₁ w : ℝ)
    (hx' : θ ≠ 0 ∨ s₀ ≠ 0 ∨ s₁ ≠ 0 ∨ w ≠ 0) :
    0 < 9 / 20 * θ ^ 2 + 9 / 10 * (w - 10 / 9 * (s₀ / 2 + s₁)) ^ 2 +
      (5 * (s₁ - 2 / 5 * s₀) ^ 2 + 126 / 5 * s₀ ^ 2) / 36 := by -- --- PROOF ---
  have a := sq_nonneg θ
  have b := sq_nonneg (w - 10 / 9 * (s₀ / 2 + s₁))
  have c := sq_nonneg (s₁ - 2 / 5 * s₀)
  have d := sq_nonneg s₀
  -- whichever coordinate is nonzero makes one square positive
  rcases hx' with h | h | h | h
  · have := sq_pos_of_ne_zero h; linarith
  · have := sq_pos_of_ne_zero h; linarith
  · by_cases h0 : s₀ = 0
    · have : (s₁ - 2 / 5 * s₀) ^ 2 = s₁ ^ 2 := by rw [h0]; ring
      have := sq_pos_of_ne_zero h; linarith
    · have := sq_pos_of_ne_zero h0; linarith
  · by_cases hs : s₀ = 0 ∧ s₁ = 0
    · have : (w - 10 / 9 * (s₀ / 2 + s₁)) ^ 2 = w ^ 2 := by rw [hs.1, hs.2]; ring
      have := sq_pos_of_ne_zero h; linarith
    · rcases not_and_or.mp hs with h0 | h1
      · have := sq_pos_of_ne_zero h0; linarith
      · by_cases h0 : s₀ = 0
        · have : (s₁ - 2 / 5 * s₀) ^ 2 = s₁ ^ 2 := by rw [h0]; ring
          have := sq_pos_of_ne_zero h1; linarith
        · have := sq_pos_of_ne_zero h0; linarith


theorem LinearSysDT.aux_faultRadiusLmiCora_posDef : -- --- CONCL ---
    let A : Mat ℝ 1 1 := 0
    let C : Mat ℝ 2 1 := 0
    let Dx : Mat ℝ 1 0 := 0                                   -- no disturbance
    let Hw : Mat ℝ 0 0 := 0
    let Dy : Mat ℝ 2 2 := 1
    let Hv : Mat ℝ 2 2 := !![1, 1 / 2; 0, 1]                 -- CORA's `F = D_y H_v`
    let P : Mat ℝ 1 1 := !![9 / 10]
    let W : Mat ℝ 1 2 := !![0, 1]                             -- CORA's `Y`
    let γ : ℝ := 1 / 2
    let Gw := Dx * Hw
    let Gv := Dy * Hv
    let TL : Matrix (Fin 1 ⊕ (Fin 0 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 0 ⊕ Fin 2)) ℝ :=
      fromBlocks (-(γ • P)) 0 0 (fromBlocks (-(Gwᵀ * Gw)) 0 0 (-(Gvᵀ * Gv)))
    let R_cora : Matrix (Fin 1 ⊕ (Fin 0 ⊕ Fin 2)) (Fin 1) ℝ :=    -- block `(3, 4)`: `F*Y'`
      fromRows (Aᵀ * P - Cᵀ * Wᵀ) (fromRows (Gwᵀ * P) (Gv * Wᵀ))
    (-(fromBlocks TL R_cora R_coraᵀ (-P))).PosDef := by -- --- PROOF ---
  intro A C Dx Hw Dy Hv P W γ Gw Gv TL R_cora
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · -- symmetric: `P`, `-γP` and the two `-MᵀM` blocks are, `R_cora` sits opposite its transpose
    have hP : P.IsHermitian := by
      ext i j; fin_cases i; fin_cases j; simp [P]
    have hGram : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ), (-(Mᵀ * M)).IsHermitian := fun M => by
      rw [← conjTranspose_eq_transpose_of_trivial]
      exact (Matrix.isHermitian_conjTranspose_mul_self M).neg
    refine Matrix.IsHermitian.neg (Matrix.IsHermitian.fromBlocks ?_ ?_ (hP.neg))
    · exact Matrix.IsHermitian.fromBlocks ((hP.smul (IsSelfAdjoint.all _)).neg) (by simp)
        (Matrix.IsHermitian.fromBlocks (hGram Gw) (by simp) (hGram Gv))
    · rw [conjTranspose_eq_transpose_of_trivial]
  set θ := x (Sum.inl (Sum.inl 0))
  set s₀ := x (Sum.inl (Sum.inr (Sum.inr 0)))
  set s₁ := x (Sum.inl (Sum.inr (Sum.inr 1)))
  set w := x (Sum.inr 0)
  have hx' : θ ≠ 0 ∨ s₀ ≠ 0 ∨ s₁ ≠ 0 ∨ w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun k => by
      rcases k with (k | k | k) | k <;> fin_cases k <;> simp [θ, s₀, s₁, w, hc.1, hc.2.1,
        hc.2.2.1, hc.2.2.2])
  -- the negated form is this sum of squares, positive off `0`
  have hpos := LinearSysDT.aux_faultRadiusLmiCora_sos θ s₀ s₁ w hx'
  -- the form, written out in the four coordinates
  simp only [star_trivial, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    Fin.sum_univ_zero, Fin.sum_univ_one]
  simp [TL, R_cora, A, C, Gw, Gv, Dx, Hw, Dy, Hv, P, W, γ, Matrix.mul_apply, Fin.sum_univ_two,
    vecHead, vecTail]
  nlinarith [hpos]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.faultRadiusLmi_cora_counterexample : -- --- CONCL ---
    let A : Mat ℝ 1 1 := 0
    let C : Mat ℝ 2 1 := 0
    let Dx : Mat ℝ 1 0 := 0                                   -- no disturbance
    let Hw : Mat ℝ 0 0 := 0
    let Dy : Mat ℝ 2 2 := 1
    let Hv : Mat ℝ 2 2 := !![1, 1 / 2; 0, 1]                 -- CORA's `F = D_y H_v`
    let P : Mat ℝ 1 1 := !![9 / 10]
    let W : Mat ℝ 1 2 := !![0, 1]                             -- CORA's `Y`
    let γ : ℝ := 1 / 2
    let Gw := Dx * Hw
    let Gv := Dy * Hv
    let TL : Matrix (Fin 1 ⊕ (Fin 0 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 0 ⊕ Fin 2)) ℝ :=
      fromBlocks (-(γ • P)) 0 0 (fromBlocks (-(Gwᵀ * Gw)) 0 0 (-(Gvᵀ * Gv)))
    let R_cora : Matrix (Fin 1 ⊕ (Fin 0 ⊕ Fin 2)) (Fin 1) ℝ :=    -- block `(3, 4)`: `F*Y'`
      fromRows (Aᵀ * P - Cᵀ * Wᵀ) (fromRows (Gwᵀ * P) (Gv * Wᵀ))
    P.PosDef ∧ (-(fromBlocks TL R_cora R_coraᵀ (-P))).PosDef ∧
      ¬ LinearSysDT.FaultRadiusLmi A C Dx Hw Dy Hv P W γ := by -- --- PROOF ---
  intro A C Dx Hw Dy Hv P W γ Gw Gv TL R_cora
  have hP : P.PosDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext i j; fin_cases i; fin_cases j; simp [P]
    · have hx0 : x 0 ≠ 0 := fun h0 => hx (funext fun i => by fin_cases i; exact h0)
      simp [P, dotProduct, mulVec]
      nlinarith [sq_pos_of_ne_zero hx0]
  refine ⟨hP, LinearSysDT.aux_faultRadiusLmiCora_posDef, fun h => ?_⟩
  -- Eq. 17 would bound the step at `θ = 0`, `s₂ = (-1/2, 1)`; it is `10/9 > 1` there
  have hle := LinearSysDT.quadForm_le_of_faultRadiusLmi A C Dx Hw Dy Hv P W γ hP h 0 0
    ![-1 / 2, 1]
  have hinv : P⁻¹ = !![10 / 9] := Matrix.inv_eq_left_inv (by
    ext i j; fin_cases i; fin_cases j; simp [P])
  have hL : P⁻¹ * W = (!![0, 10 / 9] : Mat ℝ 1 2) := by
    rw [hinv]; ext i j; fin_cases i; fin_cases j <;> simp [W]
  have he : (A - (!![0, 10 / 9] : Mat ℝ 1 2) * C) *ᵥ 0 + (Dx * Hw) *ᵥ 0 -
      ((!![0, 10 / 9] : Mat ℝ 1 2) * (Dy * Hv)) *ᵥ ![-1 / 2, 1] = ![-(10 / 9)] := by
    ext i; fin_cases i; simp [A, C, Dx, Hw, Dy, Hv]
  have hs : (Dy * Hv) *ᵥ ![-1 / 2, 1] = ![0, 1] := by
    ext i; fin_cases i <;> norm_num [Dy, Hv, mulVec, dotProduct, Fin.sum_univ_two]
  simp only [hL] at hle
  rw [he, hs] at hle
  simp [P, γ, Dx, Hw, dotProduct, mulVec] at hle
  norm_num at hle

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
