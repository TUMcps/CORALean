module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.Global.Block

@[expose] public section

/-!
# `Zonotope.absorbRounding` empties the box without losing a point

The witness is `Fin.append β γ`: the old coefficients, then one coefficient per coordinate placing
that coordinate's error in its new generator. `errorBound` rounds nothing, so the coefficient
always fits. As `ConZonotope.absorbRounding_nominal`, without the constraints.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope is contained in the nominal part of its absorbed form
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `absorbRounding`'s generator count, stated through the projection because
that is the form the goal has. -/
private theorem Zonotope.aux_sum_univ_absorbRounding {Z : Zonotope (Vec 𝕋 n)}
    (f : Fin (Z.h + n) → ℝ) :
    ∑ l : Fin Z.absorbRounding.h, f l
      = ∑ l, f (Fin.castAdd n l) + ∑ l, f (Fin.natAdd Z.h l) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.absorbRounding_nominal (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Z.construct ⊆ nominalSet Z.absorbRounding := by -- --- PROOF ---
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hz'
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound Z.I_error i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  refine Zonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append β
      (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound Z.I_error i)) (e i)),
      ?_, fun i => ?_⟩
  -- the old coefficients, then one per coordinate, each within the unit box
  · refine Fin.addCases (fun k => ?_) (fun j => ?_)
    · simpa using hβ k
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound Z.I_error)) l i
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound Z.I_error l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul']
      exact Real.Zonotope.mul_coefficient (hbound i)
    show z i + e i = _
    rw [Zonotope.aux_sum_univ_absorbRounding]
    simp only [Zonotope.absorbRounding, Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd, hz i]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
