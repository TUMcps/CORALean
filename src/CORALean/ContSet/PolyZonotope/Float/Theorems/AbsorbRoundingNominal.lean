module

public import CORALean.ContSet.PolyZonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

@[expose] public section

/-!
# `absorbRounding` empties the box without losing a point, over the nominal set

The witness is `Fin.append a (Fin.append β γ)`: the old factors, the old
independent coefficients now dependent, and one coefficient per coordinate
placing that coordinate's error in its new generator. `coefficient` supplies the
last, and `errorBound` rounds nothing, so it always fits.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set lies in the nominal set of the absorbed one
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `absorbRounding`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_absorbRounding {pZ : PolyZonotope (Vec 𝕋 n)}
    (f : Fin (pZ.h + (pZ.q + n)) → ℝ) :
    ∑ l : Fin pZ.absorbRounding.h, f l
      = ∑ l, f (Fin.castAdd (pZ.q + n) l) + ∑ l, f (Fin.natAdd pZ.h l) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

-- the error box is freed into `n` fresh factors, one per coordinate
theorem PolyZonotope.absorbRounding_nominal (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ nominalSet pZ.absorbRounding := by -- --- PROOF ---
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz'
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound pZ.I_error i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  refine PolyZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append a (Fin.append β
        (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound pZ.I_error i)) (e i))),
      Fin.elim0, ?_, fun j => j.elim0, fun i => ?_⟩
  · refine Fin.addCases (fun k => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_))
    · simpa using ha k
    · simpa only [Fin.append_left, Fin.append_right] using hβ j
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound pZ.I_error)) i l
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound pZ.I_error l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul]
      exact Real.Zonotope.mul_coefficient (hbound i)
    show z i + e i = _
    rw [PolyZonotope.aux_sum_univ_absorbRounding]
    simp only [PolyZonotope.absorbRounding, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Real.PolyZonotope.monomial_identE,
      Fin.append_left, Fin.append_right, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd, hz i]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
