module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AbsorbRounding
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.ExistsRelaxIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemRelaxIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `ConPolyZono.absorbRounding` holds the whole set in its nominal part

The witness keeps the dependent factors and appends to them one per row, the slack that row is
off by, within `[-1, 1]` since the row is within its slack (`PolyLevelSet.exists_relax_iff`), so
that every row of the constraint `PolyLevelSet.relax` now holds exactly
(`PolyLevelSet.mem_relax_iff`); and it appends to the independent coefficients one per coordinate,
placing that coordinate's error in its new generator.
`errorBound` rounds nothing, so the coefficient always fits.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

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
  -- each row's slack as a factor of its own, in `[-1, 1]`: the exact rows, relaxed, then hold
  obtain ⟨γ, hγ, hrel⟩ := (Real.PolyLevelSet.exists_relax_iff (P := cPZ.cons.nominalCore)
    cPZ.cons_eq (toRealVec cPZ.cons.b_error) a).mpr
      ((PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mp hs)
  have hleft : (fun k => Fin.append a γ (Fin.castAdd cPZ.cons.m k)) = a :=
    funext fun k => Fin.append_left a γ k
  refine ConPolyZono.mem_nominalSet_iff.mpr
    ⟨Fin.append a γ, Fin.append β
      (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cPZ.I_error i)) (e i)),
      Fin.addCases (fun k => by simpa using ha k) (fun i => by simpa using hγ i), ?_,
      (PolyLevelSet.mem_relax_iff cPZ.cons_eq _).mpr hrel, fun i => ?_⟩
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
    have hE : Real.PolyZonotope.monomial cPZ.absorbRounding.E (Fin.append a γ)
        = Real.PolyZonotope.monomial cPZ.E a :=
      funext fun l => (Real.ConPolyZono.monomial_padE cPZ.E cPZ.cons.m _ l).trans (by rw [hleft])
    -- split the independent sum at the old and the new generators
    show z i + e i = toReal (cPZ.c i)
      + (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.absorbRounding.E
          (Fin.append a γ) l)
      + ∑ j : Fin (cPZ.qI + n), toReal (Fin.append cPZ.GI
          (diagonalBlock (PolyZonotope.errorBound cPZ.I_error)) j i)
        * (Fin.append β (fun i => Real.Zonotope.coefficient
            (toReal (PolyZonotope.errorBound cPZ.I_error i)) (e i)) : Fin (cPZ.qI + n) → ℝ) j
    rw [hE, Fin.sum_univ_add, hz i]
    simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
