import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Theorems.CutShapeMulCutPrecision
import CORALean.ContSet.Ellipsoid.Real.Theorems.CutShapePosDef
import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeIff
import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The ellipsoid of the cut shape contains the ball with the parallel cut

[1, Lemma 4.3 (containment)]: the unit ball `B` cut by `|cᵀx| ≤ γ`, `‖c‖ = 1`, `γ² < 1/n`,
lies in the ellipsoid of shape [1, Eq. 16]. With the inverse of `cutShape` explicit, the
quadratic form of a point is `(n − 1)/(n(1 − γ²)) (xᵀx + λ (cᵀx)²)`,
`λ = (1 − nγ²)/((n − 1)γ²) ≥ 0`, increasing in both `xᵀx ≤ 1` and `(cᵀx)² ≤ γ²`, and `1`
at both bounds. That it is the *smallest* such
ellipsoid is the other half of the lemma, not proved.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_quad' (b l : ℝ) (c x : Vec ℝ n) :
    x ⬝ᵥ ((b • (1 + l • vecMulVec c c : Mat ℝ n n)) *ᵥ x)
      = b * (x ⬝ᵥ x + l * (c ⬝ᵥ x) ^ 2) := by -- --- PROOF ---
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul, op_smul_eq_smul]
  rw [dotProduct_comm x c]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4.3 (containment)]: `B ∩ {|cᵀx| ≤ γ}` lies in the ellipsoid of shape [1, Eq. 16]. -/
theorem Ellipsoid.cutShape_contains {c : Vec ℝ n} (hc : c ⬝ᵥ c = 1) {γ : ℝ}
    (hn : 2 ≤ n) (hγ : 0 < γ) (hγn : (n : ℝ) * γ ^ 2 < 1) :
    {x : Vec ℝ n | ‖x‖₂ ≤ 1 ∧ |c ⬝ᵥ x| ≤ γ}
      ⊆ (Ellipsoid.ofShape (Ellipsoid.cutShape n c γ) 0).construct := by -- --- PROOF ---
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have h2 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  rintro x ⟨hx, hcx⟩
  -- membership is the quadratic form of the explicit inverse
  rw [Ellipsoid.mem_ofShape_iff (Ellipsoid.cutShape_posDef hc hn hγ hγn), sub_zero,
    inv_eq_right_inv (Ellipsoid.cutShape_mul_cutPrecision hc hn hγ hγn)]
  unfold Ellipsoid.cutPrecision
  rw [Ellipsoid.aux_quad']
  -- `x·x ≤ 1` and `(c·x)² ≤ γ²` bound the form by its value `1` at the extremes
  have hxx : x ⬝ᵥ x ≤ 1 := by
    unfold norm₂ at hx
    rw [Real.sqrt_le_iff] at hx
    simp only [dotProduct, sq] at hx ⊢
    linarith [hx.2]
  have hct : (c ⬝ᵥ x) ^ 2 ≤ γ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcx 2
  have hl : 0 ≤ (1 - (n : ℝ) * γ ^ 2) / (((n : ℝ) - 1) * γ ^ 2) :=
    div_nonneg (by linarith) (by positivity)
  -- the form is increasing in both, and equals `1` at the bounds
  have hb : 0 < ((n : ℝ) - 1) / ((n : ℝ) * (1 - γ ^ 2)) := by positivity
  have hone : ((n : ℝ) - 1) / ((n : ℝ) * (1 - γ ^ 2))
      * (1 + (1 - (n : ℝ) * γ ^ 2) / (((n : ℝ) - 1) * γ ^ 2) * γ ^ 2) = 1 := by
    field_simp
    ring
  calc ((n : ℝ) - 1) / ((n : ℝ) * (1 - γ ^ 2))
        * (x ⬝ᵥ x + (1 - (n : ℝ) * γ ^ 2) / (((n : ℝ) - 1) * γ ^ 2) * (c ⬝ᵥ x) ^ 2)
      ≤ ((n : ℝ) - 1) / ((n : ℝ) * (1 - γ ^ 2))
        * (1 + (1 - (n : ℝ) * γ ^ 2) / (((n : ℝ) - 1) * γ ^ 2) * γ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hxx (mul_le_mul_of_nonneg_left hct hl)) hb.le
    _ = 1 := hone

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
