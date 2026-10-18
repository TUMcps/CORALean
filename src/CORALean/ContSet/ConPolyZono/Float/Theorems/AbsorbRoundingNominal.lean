module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AbsorbRounding
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecRelax
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol

@[expose] public section

/-!
# `ConPolyZono.absorbRounding` holds the whole set in its nominal part

The witness keeps the dependent factors and appends to them one per row, the slack that row is
off by (`(b - (A μ)ᵢ) / b_error`, within `[-1, 1]` since the row is within its slack, and `0`
where there is none), so that every row now holds exactly (`mulVec_relax`); and it appends to the
independent coefficients one per coordinate, placing that coordinate's error in its new generator.
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
  -- each row's slack, as the value of the factor `absorbRounding` gives it
  set row : Fin cPZ.m → ℝ := fun i => (toRealMat cPZ.A *ᵥ Real.PolyZonotope.monomial cPZ.R a) i
  set γ : Fin cPZ.m → ℝ := fun i => if toReal (cPZ.b_error i) = 0 then 0
    else (toReal (cPZ.b i) - row i) / toReal (cPZ.b_error i) with hγ
  have hleft : (fun k => Fin.append a γ (Fin.castAdd cPZ.m k)) = a :=
    funext fun k => Fin.append_left a γ k
  -- the stored matrix with its slack columns reads back as the relaxed one
  have hA : toRealMat cPZ.absorbRounding.A
      = (Real.ConPolyZono.relax cPZ.nominalCore (toRealVec cPZ.b_error)).A := by
    funext i l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · simp only [toRealMat, ConPolyZono.absorbRounding, Real.ConPolyZono.relax, Fin.append_left]
    · simp only [toRealMat, ConPolyZono.absorbRounding, Real.ConPolyZono.relax, Fin.append_right,
        toReal_diagonalBlock, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  refine ConPolyZono.mem_nominalSet_iff.mpr
    ⟨Fin.append a γ, Fin.append β
      (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cPZ.I_error i)) (e i)),
      ?_, ?_, fun i => ?_, fun i => ?_⟩
  -- the old factors, then one slack factor per row, each within the unit box
  · refine Fin.addCases (fun k => ?_) (fun i => ?_)
    · simpa using ha k
    · rw [Fin.append_right]
      by_cases h0 : toReal (cPZ.b_error i) = 0
      · simp [hγ, h0]
      · simp only [hγ, if_neg h0, abs_div]
        rw [div_le_one (abs_pos.mpr h0), abs_sub_comm]
        exact hs i
  -- the old independent coefficients, then one per coordinate, each within the unit box
  · refine Fin.addCases (fun k => ?_) (fun j => ?_)
    · simpa using hβ k
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- every row now holds exactly, its slack factor making up what it was off by
  · have hrow := Real.ConPolyZono.mulVec_relax cPZ.nominalCore (toRealVec cPZ.b_error)
      (Fin.append a γ) i
    rw [hleft, Fin.append_right] at hrow
    have hval : (toRealMat cPZ.absorbRounding.A *ᵥ Real.PolyZonotope.monomial
        cPZ.absorbRounding.R (Fin.append a γ)) i = toReal (cPZ.b i) := by
      rw [hA]
      refine hrow.trans ?_
      show row i + toReal (cPZ.b_error i) * γ i = _
      -- a row with no slack was met exactly; any other is made up by its slack factor
      by_cases h0 : toReal (cPZ.b_error i) = 0
      · have h := hs i
        rw [h0, abs_zero] at h
        have h' := abs_nonpos_iff.mp h
        simp only [hγ, if_pos h0, mul_zero, add_zero]
        linarith
      · simp only [hγ, if_neg h0]
        rw [mul_div_cancel₀ _ h0]
        ring
    show |(toRealMat cPZ.absorbRounding.A *ᵥ Real.PolyZonotope.monomial cPZ.absorbRounding.R
        (Fin.append a γ)) i - toReal (cPZ.b i)| ≤ |toReal (zero : 𝕋)|
    rw [hval, sub_self, abs_zero]
    exact abs_nonneg _
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound cPZ.I_error)) l i
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cPZ.I_error l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul']
      exact Real.Zonotope.mul_coefficient (hbound i)
    have hE : Real.PolyZonotope.monomial cPZ.absorbRounding.E (Fin.append a γ)
        = Real.PolyZonotope.monomial cPZ.E a :=
      funext fun l => (Real.ConPolyZono.monomial_padE cPZ.E cPZ.m _ l).trans (by rw [hleft])
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
