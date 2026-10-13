module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `Zonotope.reduceBy` carries the coefficients of the kept generators over

`Zonotope.reduceBy_outer_refines` says the reduction contains the exact one as a set. A
caller that also constrains the coefficients of the kept generators needs more: the
witness for a point of `Z` at the coefficients `β` can be taken to agree with `β` on the kept
generators, the fresh box coefficients rescaling what the dropped ones contributed to the
rounded-up radius. This states that, as an equality of the whole generator sums, so that
every coordinate of a lifted zonotope is read at once.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceBy_coeff (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (β : Fin Z.h → ℝ)
    (hβ : ∀ j, |β j| ≤ 1) :
    ∃ ξ : Fin (q + n) → ℝ, (∀ j, |ξ j| ≤ 1) ∧ (∀ l, ξ (Fin.castAdd n l) = β (part.left l))
      ∧ ∀ i, ∑ j, toReal (Z.G j i) * β j
        = ∑ j : Fin (q + n), toReal ((Z.reduceBy part).G j i) * ξ j := by -- --- PROOF ---
  -- the dropped reach is nonnegative and inside the rounded radius
  have hnonneg : ∀ i, (0:ℝ) ≤ ∑ l, |toReal (Z.G (part.right l) i)| :=
    fun i => Finset.sum_nonneg fun l _ => abs_nonneg _
  have hle : ∀ i, (∑ l, |toReal (Z.G (part.right l) i)|)
      ≤ toReal (radius (fun i l => Z.G (part.right l) i) i) :=
    fun i => sum_abs_le_radius (d := fun i l => Z.G (part.right l) i) i
  -- what the dropped generators contribute at coordinate `i`, inside the rounded radius
  have hbound : ∀ i, |∑ l, toReal (Z.G (part.right l) i) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G (part.right l) i) i) := by
    intro i
    refine le_trans ?_ (hle i)
    calc |∑ l, toReal (Z.G (part.right l) i) * β (part.right l)|
        ≤ ∑ l, |toReal (Z.G (part.right l) i) * β (part.right l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |toReal (Z.G (part.right l) i)| * |β (part.right l)| := by simp_rw [abs_mul]
      _ ≤ ∑ l, |toReal (Z.G (part.right l) i)| := Finset.sum_le_sum fun l _ => by
          simpa using mul_le_mul_of_nonneg_left (hβ (part.right l))
            (abs_nonneg (toReal (Z.G (part.right l) i)))
  -- the witness: kept coefficients, then one per coordinate scaled to the dropped reach
  refine ⟨Fin.append (fun l => β (part.left l)) (fun i =>
      Real.Zonotope.coefficient (toReal (radius (fun i l => Z.G (part.right l) i) i))
        (∑ l, toReal (Z.G (part.right l) i) * β (part.right l))), ?_, fun l => ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun i => ?_)
    · simpa using hβ (part.left l)
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one ((hnonneg i).trans (hle i)) (hbound i)
  · simp
  -- the generator sums agree, the box block through its diagonal
  · rw [part.sum_split₂ fun j => toReal (Z.G j i) * β j, Fin.sum_univ_add]
    simp only [Zonotope.reduceBy, Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [Real.Zonotope.sum_diagonal_mul']
    simp only [toRealVec]
    rw [Real.Zonotope.mul_coefficient (hbound i)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
