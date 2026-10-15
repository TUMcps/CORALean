module

public import CORALean.ContSet.ConPolyZono.Float.Operations.QuadMap
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.PolyZonotope.Float.Theorems.BilinGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

@[expose] public section

/-!
# The float `quadMap` of a constrained polynomial zonotope encloses the image

A point `z + e` of the set, `z` nominal at the factors `a` and coefficients `β`, is the
dependent form's nominal point at `a' = [a; β; e / bound]`, whose first block is `a`, so `a'`
meets the padded constraints. The quadratic image of that point is the exact layer's
`quadMapDep` at `a'` (`quadMapDep_point`), which is the stored image at `a'` plus each
generator's rounding against a monomial, inside the error box. Outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A stored generator of the float `quadMapDep` is off the exact bilinear form by at most its
gap. -/
theorem ConPolyZono.aux_quadMapG_close (Q : Fin k → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n))
    (i : Fin k) (l : Fin ((pZ.h + 1) * (pZ.h + 1))) :
    |Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal pZ) l i
        - toReal (PolyZonotope.quadMapGDown Q pZ i l)|
      ≤ toReal (PolyZonotope.quadMapGDiff Q pZ i l) :=
  PolyZonotope.bilinG_close Q pZ pZ i l

/-- The dependent form of a float polynomial zonotope, at its factors `a`, then the coefficients
`β`, then the error coordinates, is the nominal point plus the error. -/
theorem ConPolyZono.aux_dependent_point (pZ : PolyZonotope (Vec 𝕋 n)) (a : Fin pZ.p → ℝ)
    (β : Fin pZ.q → ℝ) (e : Vec ℝ n)
    (hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound pZ.I_error i)) (i : Fin n) :
    toReal (pZ.c i) + (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
        + (∑ j, toReal (pZ.GI j i) * β j) + e i
      = toReal (pZ.absorbRounding.c i)
        + ∑ l : Fin pZ.absorbRounding.h, toReal (pZ.absorbRounding.G l i)
        * Real.PolyZonotope.monomial pZ.absorbRounding.E (Fin.append a (Fin.append β
          fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound pZ.I_error i)) (e i)))
          l := by -- --- PROOF ---
  -- the diagonal block reproduces `e` exactly, coordinate by coordinate
  have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound pZ.I_error)) i l
      * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound pZ.I_error l)) (e l)
        = e i := by
    rw [Real.Zonotope.sum_diagonal_mul]
    exact Real.Zonotope.mul_coefficient (hbound i)
  have hsplit : ∀ f : Fin (pZ.h + (pZ.q + n)) → ℝ, ∑ l : Fin pZ.absorbRounding.h, f l
      = ∑ l, f (Fin.castAdd (pZ.q + n) l) + ∑ l, f (Fin.natAdd pZ.h l) :=
    fun f => Fin.sum_univ_add f
  rw [hsplit]
  simp only [PolyZonotope.absorbRounding, Real.PolyZonotope.monomial_plusE_left,
    Real.PolyZonotope.monomial_plusE_right, Real.PolyZonotope.monomial_identE,
    Fin.append_left, Fin.append_right]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
  rw [hd]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMap_outer (Q : Fin k → Mat 𝕋 n n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun i => toRealMat (Q i)) '' cPZ.construct
      ⊆ (cPZ.quadMap Q).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨z, hz', e, he, rfl⟩, rfl⟩
  obtain ⟨a, β, ha, hβ, hs, hz⟩ := ConPolyZono.mem_nominalSet_iff.mp hz'
  set D := cPZ.toPolyZonotope.absorbRounding with hD
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound cPZ.I_error i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  -- the factors of the dependent form: `a`, then `β`, then the error box's coordinates
  set a' : Fin (cPZ.p + (cPZ.qI + n)) → ℝ := Fin.append a (Fin.append β
    fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound cPZ.I_error i)) (e i))
    with ha'
  have ha'b : ∀ l, |a' l| ≤ 1 := by
    refine Fin.addCases (fun l => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_))
    · simpa [ha'] using ha l
    · simpa only [ha', Fin.append_left, Fin.append_right] using hβ j
    · simp only [ha', Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- the point is the dependent form's nominal point at `a'`
  have hpt : Real.PolyZonotope.point (nominal D) a' = z + e := by
    funext i
    have h := ConPolyZono.aux_dependent_point cPZ.toPolyZonotope a β e hbound i
    show toReal (D.c i) + (∑ l, Real.PolyZonotope.monomial D.E a' l • fun r => toReal (D.G l r)) i
      = z i + e i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hz i]
    refine Eq.trans ?_ h.symm
    exact congrArg _ (Finset.sum_congr rfl fun l _ => mul_comm _ _)
  -- the stored generators against the monomials at `a'`, off by the box's share
  have hbox := PolyZonotope.mem_generatorError_monomial (E := PolyZonotope.quadMapE D)
    (ConPolyZono.aux_quadMapG_close Q D) ha'b
  refine ⟨fun i => toReal ((cPZ.quadMap Q).c i)
      + (∑ l : Fin ((D.h + 1) * (D.h + 1)), toReal (PolyZonotope.quadMapGDown Q D i l)
          * Real.PolyZonotope.monomial (PolyZonotope.quadMapE D) a' l)
      + ∑ j : Fin 0, toReal ((cPZ.quadMap Q).GI j i) * (Fin.elim0 j : ℝ),
    ConPolyZono.mem_nominalSet_iff.mpr ⟨a', Fin.elim0, ha'b, fun j => j.elim0, ?_, fun _ => rfl⟩,
    _, hbox, ?_⟩
  · -- the padded constraints read only the first block, which is `a`
    show Real.ConPolyZono.holds (toRealMat cPZ.A) cPZ.b.nominal
      (Real.ConPolyZono.padE cPZ.R (cPZ.qI + n)) a'
    rw [Real.ConPolyZono.holds_padE_iff]
    simp only [ha', Fin.append_left]
    exact hs
  · -- the image is the exact layer's `quadMapDep` at `a'`, the stored one plus the box's share
    funext i
    have hq := Real.PolyZonotope.quadMapDep_point (fun k => toRealMat (Q k)) (nominal D) a'
    rw [hpt] at hq
    rw [← hq]
    -- stored generators plus their rounding are the exact ones, monomial by monomial
    have hsum : (∑ l : Fin ((D.h + 1) * (D.h + 1)), toReal (PolyZonotope.quadMapGDown Q D i l)
          * Real.PolyZonotope.monomial (PolyZonotope.quadMapE D) a' l)
        + (∑ l : Fin ((D.h + 1) * (D.h + 1)),
            (Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal D) l i
              - toReal (PolyZonotope.quadMapGDown Q D i l))
                * Real.PolyZonotope.monomial (PolyZonotope.quadMapE D) a' l)
        = ∑ l : Fin ((D.h + 1) * (D.h + 1)),
            Real.PolyZonotope.quadMapG (fun k => toRealMat (Q k)) (nominal D) l i
              * Real.PolyZonotope.monomial (PolyZonotope.quadMapE D) a' l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [Pi.add_apply, ConPolyZono.quadMap, PolyZonotope.quadMapDep, PolyZonotope.bilin,
      toReal_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add]
    simp only [Real.PolyZonotope.point, Real.PolyZonotope.quadMapDep, Real.PolyZonotope.bilin,
      Pi.zero_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zero_add]
    exact hsum.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
