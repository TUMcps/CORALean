import CORALean.Arithmetic.Float.ContSet.Zonotope.API
import CORALean.Arithmetic.Real.ContSet.Zonotope.Proofs.Coefficient

/-!
# `Zonotope.reduce` keeps the set it had

The exact argument with one inequality where it had an equality: the diagonal
block need only *cover* the absorbed generators, so rounding its radius up costs
precision and nothing else. The box is untouched, hence `mono_subset`.

Soundness holds for every partition, exactly as over ℝ; a selection rule still
carries no proof obligation.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet
open CORALean.Arithmetic.Real.Zonotope.Proofs

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h q r : ℕ}

/-- What the absorbed generators contribute, so what the block must cover. -/
theorem abs_absorbed_le_radius (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) {β : Vec ℝ h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ l, toReal (Z.G i (part.right l)) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) := by
  exact abs_sum_le_radius (d := fun i l => Z.G i (part.right l))
    (fun _ _ => le_refl _) (fun l => hβ (part.right l)) i

theorem reduce_nominal (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    nominalSet Z ⊆ nominalSet (Z.reduce part) := by
  rintro x ⟨β, hβ, hx⟩
  have hbound := abs_absorbed_le_radius Z part hβ
  have hnonneg : ∀ i, (0:ℝ) ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) :=
    fun i => (abs_nonneg _).trans (hbound i)
  refine ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      coefficient (toReal (radius (fun i l => Z.G i (part.right l)) i))
        (∑ l, toReal (Z.G i (part.right l)) * β (part.right l))), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact abs_coefficient_le_one (hnonneg i) (hbound i)
  · rw [hx i, part.sum_split₂ fun j => (nominal Z).G i j * β j]
    simp only [Zonotope.reduce, Zonotope.nominal_c, Zonotope.nominal_G, toRealVec, toRealMat,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [sum_diagonal_mul]
    simp only [toRealVec]
    rw [mul_coefficient (hbound i)]

theorem reduce_outer (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct :=
  mono_subset (reduce_nominal Z part) (subset_refl _)

end CORALean.Arithmetic.Float.Zonotope.Proofs
