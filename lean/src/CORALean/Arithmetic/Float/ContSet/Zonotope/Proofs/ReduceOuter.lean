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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h q r : ℕ}

/-- What the absorbed generators contribute, so what the block must cover. -/
theorem abs_absorbed_le_radius (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) {β : Vec ℝ Z.h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ l, toReal (Z.G i (part.right l)) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) := by
  exact abs_sum_le_radius (d := fun i l => Z.G i (part.right l))
    (fun _ _ => le_refl _) (fun l => hβ (part.right l)) i

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `reduce`'s generator count; see `Zonotope.sum_split_nominal`. -/
theorem sum_univ_reduce {Z : Zonotope 𝕋 n} {part : Split (Fin Z.h) into (Fin q) and (Fin r)}
    (f : Fin (q + n) → ℝ) :
    ∑ j : Fin (Z.reduce part).h, f j = ∑ j, f (Fin.castAdd n j) + ∑ j, f (Fin.natAdd q j) :=
  Fin.sum_univ_add f

theorem reduce_nominal (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    nominalSet Z ⊆ nominalSet (Z.reduce part) := by
  rintro x hx'
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx'
  have hbound := abs_absorbed_le_radius Z part hβ
  have hnonneg : ∀ i, (0:ℝ) ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) :=
    fun i => (abs_nonneg _).trans (hbound i)
  refine Zonotope.mem_nominalSet_iff.mpr ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      coefficient (toReal (radius (fun i l => Z.G i (part.right l)) i))
        (∑ l, toReal (Z.G i (part.right l)) * β (part.right l))), ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact abs_coefficient_le_one (hnonneg i) (hbound i)
  · rw [hx i, part.sum_split₂ fun j => toReal (Z.G i j) * β j, sum_univ_reduce]
    simp only [Zonotope.reduce, Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [sum_diagonal_mul]
    simp only [toRealVec]
    rw [mul_coefficient (hbound i)]

theorem reduce_outer (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct :=
  mono_subset (reduce_nominal Z part) (subset_refl _)

end CORALean.Arithmetic.Float.Zonotope.Proofs
