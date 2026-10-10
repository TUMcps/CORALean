import CORALean.ContSet.Zonotope.Real.Operations.OfEchelon
import CORALean.ContSet.Zonotope.Real.Operations.ReduceScottStep
import Mathlib.Algebra.BigOperators.Fin

/-!
# One step of the reduction of [1, Sec. 4.3 (new reduction)] encloses

`{[T TR], c} ⊆ {[T' T'R'], c}` for `(T', R') = reduceScottStep T R ind`, at every `T` and every
chosen column. Write a point as `c + Tβ + Σ_l γ_l T r_l`. The chosen column's term joins the
first block, `T(β + γ_ind r) = T(I + diag|r|)δ` with `δ_i = (β_i + γ_ind r_i)/(1 + |r_i|)`,
and `|δ_i| ≤ 1` because `|β_i| ≤ 1` and `|γ_ind| ≤ 1`. That is Chisci et al.'s parallelotope
`X̃ ⊇ X`. Every other term is unchanged, `T' r'_l = T(I + diag|r|)(I + diag|r|)⁻¹ r_l = T r_l`.
[1] reads `T` invertible and `‖r‖∞ ≤ 1` off the Gauss-Jordan step; the enclosure needs neither.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `{[T TR], c}`, its coefficient vector split at the two blocks. -/
theorem Zonotope.aux_ofEchelon_sum {n k : ℕ} (c : Vec ℝ n) (T : Mat ℝ n n)
    (R : Fin k → Vec ℝ n) (β : Fin (n + k) → ℝ) :
    c + ∑ a, β a • Fin.append (fun i a => T a i) (fun l => T *ᵥ R l) a
      = c + T *ᵥ (fun i => β (Fin.castAdd k i))
        + ∑ l, β (Fin.natAdd n l) • (T *ᵥ R l) := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  -- the first block is `T` applied to its coefficients
  have h1 : ∑ i : Fin n, β (Fin.castAdd k i) • (fun a => T a i)
      = T *ᵥ (fun i => β (Fin.castAdd k i)) := by
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h1, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: one step of the reduction, at any `T` and any chosen column,
encloses. -/
theorem Zonotope.ofEchelon_reduceScottStep_outer {n k : ℕ} (c : Vec ℝ n) (T : Mat ℝ n n)
    (R : Fin (k + 1) → Vec ℝ n) (ind : Fin (k + 1)) :
    (Zonotope.ofEchelon c T R).construct
      ⊆ (Zonotope.ofEchelon c (Zonotope.reduceScottStep T R ind).1
          (Zonotope.reduceScottStep T R ind).2).construct := by -- --- PROOF ---
  rintro x ⟨(β : Fin (n + (k + 1)) → ℝ), hβ, rfl⟩
  set r := R ind with hr
  set d : Fin n → ℝ := fun i => 1 + |r i| with hd
  have hdpos : ∀ i, 0 < d i := fun i => by simp only [hd]; positivity
  -- `I + diag|r|` times its inverse
  have hDDinv : ∀ v : Vec ℝ n,
      diagonal d *ᵥ (diagonal (fun i => (d i)⁻¹) *ᵥ v) = v := fun v => by
    funext i
    simp [Matrix.mulVec_diagonal, mul_inv_cancel_left₀ (hdpos i).ne']
  -- the new coefficients: the chosen column folded into the first block
  set δ : Fin n → ℝ := fun i => (β (Fin.castAdd (k + 1) i) + β (Fin.natAdd n ind) * r i) / d i
    with hδ
  have hDδ : diagonal d *ᵥ δ
      = (fun i => β (Fin.castAdd (k + 1) i)) + β (Fin.natAdd n ind) • r := by
    funext i
    simp [hδ, Matrix.mulVec_diagonal, mul_div_cancel₀ _ (hdpos i).ne']
  refine ⟨Fin.append δ fun l => β (Fin.natAdd n (ind.succAbove l)), fun a => ?_, ?_⟩
  · -- `|δ_i| ≤ 1`, the parallelotope's own bound, and the kept coefficients unchanged
    refine Fin.addCases (fun i => ?_) (fun l => ?_) a
    · -- `|β_i + γ r_i| ≤ 1 + |r_i|`
      rw [Fin.append_left, hδ, abs_div, abs_of_pos (hdpos i), div_le_one (hdpos i)]
      calc |β (Fin.castAdd (k + 1) i) + β (Fin.natAdd n ind) * r i|
          ≤ |β (Fin.castAdd (k + 1) i)| + |β (Fin.natAdd n ind)| * |r i| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ 1 + 1 * |r i| := by
            gcongr
            · exact hβ _
            · exact hβ _
        _ = d i := by simp [hd]
    · rw [Fin.append_right]; exact hβ _
  · -- the same point: the chosen term moves into the first block, the rest stay
    show c + ∑ a, β a • Fin.append (fun i a => T a i) (fun l => T *ᵥ R l) a
      = c + ∑ a, Fin.append δ (fun l => β (Fin.natAdd n (ind.succAbove l))) a
          • Fin.append (fun i a => (T * diagonal d) a i)
              (fun l => (T * diagonal d) *ᵥ (diagonal (fun i => (d i)⁻¹) *ᵥ R (ind.succAbove l)))
              a
    rw [Zonotope.aux_ofEchelon_sum, Zonotope.aux_ofEchelon_sum]
    simp only [Fin.append_left, Fin.append_right]
    simp only [← Matrix.mulVec_mulVec, hDDinv, hDδ, Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [Fin.sum_univ_succAbove _ ind]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
