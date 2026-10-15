module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AbsorbRounding
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `ConPolyZono.absorbRounding` holds the whole set in its nominal part

The witness keeps the dependent factors and appends to the independent coefficients one per
coordinate, placing that coordinate's error in its new generator. `errorBound` rounds nothing, so
the coefficient always fits.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the set, box included, is a nominal point of `absorbRounding`. -/
theorem ConPolyZono.absorbRounding_nominal (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ nominalSet cPZ.absorbRounding := by -- --- PROOF ---
  -- a point is a nominal point plus an error within the box
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hs, hz⟩ := ConPolyZono.mem_nominalSet_iff.mp hz'
  -- each coordinate of the error is within `errorBound`, which rounds nothing
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound cPZ.I_error i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  refine ConPolyZono.mem_nominalSet_iff.mpr
    ⟨a, Fin.append β
      (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cPZ.I_error i)) (e i)),
      ha, ?_, hs, fun i => ?_⟩
  -- the old independent coefficients, then one per coordinate, each within the unit box
  · refine Fin.addCases (fun k => ?_) (fun j => ?_)
    · simpa using hβ k
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound cPZ.I_error)) l i
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cPZ.I_error l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul']
      exact Real.Zonotope.mul_coefficient (hbound i)
    -- split the independent sum at the old and the new generators
    show z i + e i = toReal (cPZ.c i)
      + (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E a l)
      + ∑ j : Fin (cPZ.qI + n), toReal (Fin.append cPZ.GI
          (diagonalBlock (PolyZonotope.errorBound cPZ.I_error)) j i)
        * (Fin.append β (fun i => Real.Zonotope.coefficient
            (toReal (PolyZonotope.errorBound cPZ.I_error i)) (e i)) : Fin (cPZ.qI + n) → ℝ) j
    rw [Fin.sum_univ_add, hz i]
    simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
