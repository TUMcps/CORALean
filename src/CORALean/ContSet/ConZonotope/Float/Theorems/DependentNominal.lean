import CORALean.ContSet.ConZonotope.Float.Operations.Dependent
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.HPolytope.Float.Operations.MemPadLeftIff
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
import CORALean.Global.Block

/-!
# `dependent` empties the box without losing a point, over the nominal set

The witness is `Fin.append β γ`: the old coefficients, which keep meeting the constraints, and one
coefficient per coordinate placing that coordinate's error in its new generator. The new block is
free, so the padded constraints ask nothing of it, and `errorBound` rounds nothing, so the
coefficient always fits.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `dependent`'s generator count, stated through the projection because
that is the form the goal has. -/
theorem ConZonotope.aux_sum_univ_dependent {cZ : ConZonotope 𝕋 (Vec 𝕋 n)} (f : Fin (cZ.h + n) → ℝ) :
    ∑ l : Fin cZ.dependent.h, f l
      = ∑ l, f (Fin.castAdd n l) + ∑ l, f (Fin.natAdd cZ.h l) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.dependent_nominal (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ nominalSet cZ.dependent := by -- --- PROOF ---
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨β, hβ, hP, hz⟩ := ConZonotope.mem_nominalSet_iff.mp hz'
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound cZ.E i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  refine ConZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append β
      (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cZ.E i)) (e i)),
      ?_, ?_, fun i => ?_⟩
  -- the old coefficients, then one per coordinate, each within the unit box
  · refine Fin.addCases (fun k => ?_) (fun j => ?_)
    · simpa using hβ k
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- the constraints read only the old block
  · refine HPolytope.mem_padLeft_iff.mpr ?_
    rw [blockLeft_append]
    exact hP
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound cZ.E)) l i
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cZ.E l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul']
      exact Real.Zonotope.mul_coefficient (hbound i)
    show z i + e i = _
    rw [ConZonotope.aux_sum_univ_dependent]
    simp only [ConZonotope.dependent, Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd, hz i]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
