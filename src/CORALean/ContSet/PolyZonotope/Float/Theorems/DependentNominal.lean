import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

/-!
# `dependent` empties the box without losing a point, over the nominal set

The witness is `Fin.append a (Fin.append β γ)`: the old factors, the old
independent coefficients now dependent, and one coefficient per coordinate
placing that coordinate's error in its new generator. `coefficient` supplies the
last, and `errorBound` rounds nothing, so it always fits.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `dependent`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_dependent {PZ : PolyZonotope 𝕋 n}
    (f : Fin (PZ.h + (PZ.q + n)) → ℝ) :
    ∑ l : Fin PZ.dependent.h, f l
      = ∑ l, f (Fin.castAdd (PZ.q + n) l) + ∑ l, f (Fin.natAdd PZ.h l) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

-- the error box is freed into `n` fresh factors, one per coordinate
theorem PolyZonotope.dependent_nominal (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ nominalSet PZ.dependent := by
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz'
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound PZ.err i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  refine PolyZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append a (Fin.append β
        (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound PZ.err i)) (e i))),
      Fin.elim0, ?_, fun j => j.elim0, fun i => ?_⟩
  · refine Fin.addCases (fun k => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_))
    · simpa using ha k
    · simpa only [Fin.append_left, Fin.append_right] using hβ j
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound PZ.err)) i l
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound PZ.err l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul]
      exact Real.Zonotope.mul_coefficient (hbound i)
    show z i + e i = _
    rw [PolyZonotope.aux_sum_univ_dependent]
    simp only [PolyZonotope.dependent, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Real.PolyZonotope.monomial_identE,
      Fin.append_left, Fin.append_right, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd, hz i]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
