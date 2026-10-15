module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A polytope as a spectrahedral shadow, over a floating-point scalar

CORA's `@polytope/spectraShadow`: one `1 × 1` block `d_j - C_j x` per row of the stacked
`C = [A; Ae; -Ae]`, `d = [b; be; -be]`, as the diagonal `A₀ = diag(d)`, `Aᵢ = -diag(C(:,i))`.
The equality rows are the pair `Ae x ≤ be`, `-Ae x ≤ -be` the float polytope denotes, so the
stacked right-hand side is `[b; be; -be]`. Every entry is an existing entry, a negation or a
`zero`, `one`: nothing rounds, and the error box is the polytope's own. The shadow contains the
polytope.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A diagonal inequality read as reals: the diagonal of the slacks. -/
theorem HPolytope.aux_lmi_diag {k : ℕ} (d : Fin k → 𝕋) (C : Fin n → Fin k → 𝕋) (x : Vec ℝ n) :
    (toRealMat (fun p q => if p = q then d p else zero) +
      ∑ i, x i • toRealMat (fun p q => if p = q then neg (C i p) else zero) : Mat ℝ k k)
      = diagonal fun p => toReal (d p) - ∑ i, x i * toReal (C i p) := by -- --- PROOF ---
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp [toRealMat, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, toReal_neg,
      sub_eq_add_neg, Finset.sum_neg_distrib]
  · simp [toRealMat, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hpq, toReal_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- At a point of the polytope's nominal part the stored inequality is positive semidefinite. -/
theorem HPolytope.posSemidef_spectraShadow (P : HPolytope 𝕋 (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ P.nominal.construct) :
    (toRealMat P.spectraShadow.A₀
      + ∑ i, x i • toRealMat (P.spectraShadow.A i)).PosSemidef := by -- --- PROOF ---
  -- the matrix is the diagonal of the slacks
  have hM := HPolytope.aux_lmi_diag (n := n) (𝕋 := 𝕋)
    (Fin.append P.b (Fin.append P.be fun r => neg (P.be r)))
    (fun i => Fin.append (fun r => P.A r i)
      (Fin.append (fun r => P.Ae r i) fun r => neg (P.Ae r i))) x
  refine Eq.mpr (congrArg Matrix.PosSemidef hM) (posSemidef_diagonal_iff.mpr ?_)
  obtain ⟨hA, hAe⟩ := HPolytope.mem_nominal_iff.mp hx
  -- the three row groups
  intro p
  refine Fin.addCases (fun r => ?_) (fun p' => Fin.addCases (fun r => ?_) (fun r => ?_) p') p
  · have := hA r
    simp only [Fin.append_left, mulVec, dotProduct, toRealMat] at this ⊢
    simp only [mul_comm (x _)] at this ⊢
    linarith
  · have := (hAe r).le
    simp only [Fin.append_left, Fin.append_right, mulVec, dotProduct, toRealMat] at this ⊢
    simp only [mul_comm (x _)] at this ⊢
    linarith
  · have := (hAe r).ge
    simp only [Fin.append_right, mulVec, dotProduct, toRealMat, toReal_neg] at this ⊢
    simp only [mul_comm (x _), neg_mul, Finset.sum_neg_distrib] at this ⊢
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
