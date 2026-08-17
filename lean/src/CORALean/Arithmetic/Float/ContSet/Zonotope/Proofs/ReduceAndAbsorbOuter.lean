import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.ReduceOuter
import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.AbsorbErrorOuter

/-!
# `reduceAndAbsorb` keeps the set it had

The two arguments meet in one coefficient. The absorbed generators contribute at
most `radius`, the box at most `errorRadius`, and the merged block has radius at
least their sum, so one coefficient places both at once.

Neither `mono_subset` nor `map_subset` applies: they send nominal to nominal and
box to box, whereas this moves content *out* of the box into the nominal part.
What is left in the box is the rounded centre shift, as in `absorbError`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet
open CORALean.Arithmetic.Real.Zonotope.Proofs

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n h q r : ℕ}

/-- The merged block covers the absorbed generators and the box together. -/
theorem abs_merged_le_radius (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) {β : Vec ℝ h} {e : Vec ℝ n}
    (hβ : ∀ j, |β j| ≤ 1) (he : e ∈ Z.E.construct) (i : Fin n) :
    |(∑ l, toReal (Z.G i (part.right l)) * β (part.right l))
        + (e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2)|
      ≤ toReal (addUp (radius (fun i l => Z.G i (part.right l)) i) (Z.errorRadius i)) := by
  have hgen := abs_absorbed_le_radius Z part hβ i
  have hbox := abs_sub_mid_le_errorRadius Z he i
  have hsum := add_le_addUp (radius (fun i l => Z.G i (part.right l)) i) (Z.errorRadius i)
  exact le_trans (abs_add_le _ _) (by linarith)

theorem reduceAndAbsorb_outer (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduceAndAbsorb part).construct := by
  rintro _ ⟨z, ⟨β, hβ, hz⟩, e, he, rfl⟩
  have hmerged := abs_merged_le_radius Z part hβ he
  have hnonneg : ∀ i, (0:ℝ) ≤
      toReal (addUp (radius (fun i l => Z.G i (part.right l)) i) (Z.errorRadius i)) :=
    fun i => (abs_nonneg _).trans (hmerged i)
  refine ⟨fun i => toReal ((Z.reduceAndAbsorb part).c i)
            + ∑ j, toReal ((Z.reduceAndAbsorb part).G i j)
                * Fin.append (fun l => β (part.left l)) (fun i =>
                    coefficient (toReal (addUp (radius (fun i l => Z.G i (part.right l)) i)
                        (Z.errorRadius i)))
                      ((∑ l, toReal (Z.G i (part.right l)) * β (part.right l))
                        + (e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2))) j,
          ⟨_, ?_, fun _ => rfl⟩,
          fun i => toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i), ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact abs_coefficient_le_one (hnonneg i) (hmerged i)
  · exact Interval.sub_mem_residual (shift_brackets_mid Z)
  · funext i
    show toReal ((Z.reduceAndAbsorb part).c i)
        + ∑ j, toReal ((Z.reduceAndAbsorb part).G i j)
            * Fin.append (fun l => β (part.left l)) (fun i =>
                coefficient (toReal (addUp (radius (fun i l => Z.G i (part.right l)) i)
                    (Z.errorRadius i)))
                  ((∑ l, toReal (Z.G i (part.right l)) * β (part.right l))
                    + (e i - (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2))) j
        + (toReal (Z.c i) + (toReal (Z.E.inf i) + toReal (Z.E.sup i)) / 2
            - toReal (Z.shiftDown i))
      = z i + e i
    rw [hz i, part.sum_split₂ fun j => (nominal Z).G i j * β j]
    simp only [Zonotope.reduceAndAbsorb, Zonotope.nominal_c, Zonotope.nominal_G, toRealVec,
      toRealMat, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      toReal_diagonalBlock]
    rw [sum_diagonal_mul]
    simp only [toRealVec]
    rw [mul_coefficient (hmerged i)]
    ring

end CORALean.Arithmetic.Float.Zonotope.Proofs
